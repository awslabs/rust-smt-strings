// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Basic string representation and operations for the SMT-LIB theory of strings
//!
//! In SMT-LIB, a string is a sequence of integers in the range 0x00000 .. 0x2FFFF (inclusive).
//! This is enough to encode Unicode characters but can also include non Unicode characters.
//!
//! This module provide functions for constructing SMT string constants. It also implements
//! all operations on strings defined by the SMT-LIB standard.
//!
//! We limit the length of string constants to [i32::MAX] and the code will panic if this bound is exceeded.
//!

#![allow(clippy::many_single_char_names)]
#![allow(clippy::manual_range_contains)]

use crate::matcher::{naive_search, SearchResult};
use std::slice::Iter;
use std::{char, cmp, fmt};

/// Maximal length of a string
pub const MAX_LENGTH: i32 = i32::MAX;

/// Maximal character index
pub const MAX_CHAR: u32 = 0x2FFFF;

/// Replacement for an integer not in the range [0...0x2FFFF]
pub const REPLACEMENT_CHAR: u32 = 0xFFFD;

///
/// Internal representation of an SMT string
/// - s = a vector of SMT character. Each character is a 32bit unsigned integer
/// - maximal length = 2^31-1
///
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct SmtString {
    s: Vec<u32>,
}

/// The empty string
pub const EMPTY: SmtString = SmtString { s: vec![] };

impl SmtString {
    // internal construct
    fn make(a: Vec<u32>) -> SmtString {
        let n = a.len();
        if n > MAX_LENGTH as usize {
            panic!(
                "Cannot construct a string of length {}: max length is {}",
                n, MAX_LENGTH
            );
        }
        SmtString { s: a }
    }

    // construct from a slice
    fn make_from_slice(a: &[u32]) -> SmtString {
        Self::make(a.to_vec())
    }

    /// Check whether this is a good string
    pub fn is_good(&self) -> bool {
        let n = self.s.len();
        n < MAX_LENGTH as usize && good_string(&self.s)
    }

    /// Check whether all SMT chars are valid unicode
    pub fn is_unicode(&self) -> bool {
        all_unicode(&self.s)
    }

    /// Convert to a regular string
    /// - any char that's not a valid unicode code point is replaced by U+FFFD
    pub fn to_unicode_string(&self) -> String {
        map_to_unicode(&self.s)
    }

    /// Get the length
    pub fn len(&self) -> usize {
        self.s.len()
    }

    /// Check whether the string is empty
    pub fn is_empty(&self) -> bool {
        self.s.is_empty()
    }

    /// Get character at index i.
    /// panic if i is out of range
    pub fn char(&self, i: usize) -> u32 {
        self.s[i]
    }

    /// Iterator
    pub fn iter(&self) -> Iter<'_, u32> {
        self.s.iter()
    }
}

impl AsRef<[u32]> for SmtString {
    fn as_ref(&self) -> &[u32] {
        self.s.as_ref()
    }
}

///
/// Construct an SmtString from a UTF8 string x
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(SmtString::from(""), EMPTY);
/// assert_eq!(SmtString::from("\u{0331}"), SmtString::from(0x331));
/// ```
impl From<&str> for SmtString {
    fn from(x: &str) -> Self {
        SmtString::make(x.chars().map(|c| c as u32).collect())
    }
}

impl From<String> for SmtString {
    fn from(x: String) -> Self {
        SmtString::from(x.as_str())
    }
}

///
/// Construct an SmtString from a slice or array of integers.
///
/// Any element of a not in the range [0, 0x2ffff] is replaced by 0xfffd.
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(SmtString::from(&[97, 98, 99]), SmtString::from("abc"));
/// ```
impl From<&[u32]> for SmtString {
    fn from(a: &[u32]) -> Self {
        SmtString::make(
            a.iter()
                .map(|&x| if x <= MAX_CHAR { x } else { REPLACEMENT_CHAR })
                .collect(),
        )
    }
}

impl<const N: usize> From<&[u32; N]> for SmtString {
    fn from(a: &[u32; N]) -> Self {
        a[..].into()
    }
}

impl From<Vec<u32>> for SmtString {
    fn from(a: Vec<u32>) -> Self {
        if a.iter().all(|&x| x <= MAX_CHAR) {
            SmtString::make(a)
        } else {
            a[..].into()
        }
    }
}

///
/// Construct a single-character string from integer x.
///
/// Convert x to 0xfffd if it's not a valid character (i.e., if x is not in the range [0, 0x2ffff])
///
impl From<u32> for SmtString {
    fn from(x: u32) -> Self {
        let x = if x <= MAX_CHAR { x } else { REPLACEMENT_CHAR };
        SmtString::make(vec![x])
    }
}

///
/// Construct a single-character string from character x.
///
impl From<char> for SmtString {
    fn from(x: char) -> SmtString {
        SmtString::make(vec![x as u32])
    }
}

// State machine for parsing SMT-LIB literals
#[derive(Debug, PartialEq, Eq)]
enum State {
    Init,
    AfterSlash,
    AfterSlashU,
    AfterSlashUHex,
    AfterSlashUBrace,
}

#[derive(Debug, PartialEq, Eq)]
struct ParsingAutomaton {
    state: State,
    // SMT string under construction
    string_so_far: Vec<u32>,
    // pending + pending_idx form an escape prefix
    // (e.g., something like "\u3C") is stored in pending[0 .. 3] and pending_idx = 4
    pending: [u32; 9],
    pending_idx: usize,
    // escape code = value of the escape prefix
    escape_code: u32,
}

fn new_automaton() -> ParsingAutomaton {
    ParsingAutomaton {
        state: State::Init,
        string_so_far: Vec::new(),
        pending: [0; 9],
        pending_idx: 0,
        escape_code: 0,
    }
}

impl ParsingAutomaton {
    // add char x to the string so far
    fn push(&mut self, x: char) {
        self.string_so_far.push(x as u32);
    }

    // add char x to the pending array
    fn pending(&mut self, x: char) {
        let i = self.pending_idx;
        assert!(i < 9);
        self.pending[i] = x as u32;
        self.pending_idx += 1;
    }

    // consume character x in the Init state
    fn consume(&mut self, x: char) {
        if x == '\\' {
            self.pending(x);
            self.state = State::AfterSlash;
        } else {
            self.push(x);
        }
    }

    // add all pending characters to the string so far
    // then reset state to INIT
    fn flush_pending(&mut self) {
        let pending = &self.pending[0..self.pending_idx];
        self.string_so_far.extend_from_slice(pending);
        self.pending_idx = 0;
        self.escape_code = 0;
        self.state = State::Init;
    }

    // close the escape sequence
    fn close_escape_seq(&mut self) {
        self.string_so_far.push(self.escape_code);
        self.pending_idx = 0;
        self.escape_code = 0;
        self.state = State::Init;
    }

    // add hexadecimal character x to the pending array
    // and update the escape_code
    fn add_hex(&mut self, x: char) {
        let hex = x.to_digit(16).unwrap();
        self.escape_code = self.escape_code << 4 | hex;
        self.pending(x);
    }

    // accept a new character x
    fn accept(&mut self, x: char) {
        match self.state {
            State::Init => {
                self.consume(x);
            }
            State::AfterSlash => {
                if x == 'u' {
                    self.pending(x);
                    self.state = State::AfterSlashU;
                } else {
                    self.flush_pending();
                    self.consume(x);
                }
            }
            State::AfterSlashU => {
                if x == '{' {
                    self.pending(x);
                    self.state = State::AfterSlashUBrace;
                } else if x.is_ascii_hexdigit() {
                    self.add_hex(x);
                    self.state = State::AfterSlashUHex;
                } else {
                    self.flush_pending();
                    self.consume(x);
                }
            }
            State::AfterSlashUBrace => {
                // '}' terminates the escape sequence if we have at least one hex digit
                // (i.e.. pending_idx > 3) and the escape_code is no more than 0x2FFFF
                if x == '}' && self.pending_idx > 3 && self.escape_code <= MAX_CHAR {
                    self.close_escape_seq();
                } else if x.is_ascii_hexdigit() && self.pending_idx < 8 {
                    // can't have more than 5 hex digit after '\u{'
                    self.add_hex(x);
                } else {
                    self.flush_pending();
                    self.consume(x);
                }
            }
            State::AfterSlashUHex => {
                // end the escape sequence exactly four hex digits after '\u'
                if x.is_ascii_hexdigit() {
                    self.add_hex(x);
                    if self.pending_idx == 6 {
                        self.close_escape_seq();
                    }
                } else {
                    self.flush_pending();
                    self.consume(x);
                }
            }
        }
    }
}

///
/// Parse a string literal in the SMT-LIB syntax and
/// convert it to an SmtString.
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(parse_smt_literal("abc"), SmtString::from(&[97, 98, 99]));
/// assert_eq!(parse_smt_literal(r"a\u0000C"), SmtString::from(&[97, 0, 67]));
///
/// // bad escape sequences are copied verbatim
/// assert_eq!(parse_smt_literal(r"\u2CA"), SmtString::from(&[92, 117, 50, 67, 65]));
/// ```
///
pub fn parse_smt_literal(a: &str) -> SmtString {
    let mut parser = new_automaton();
    for x in a.chars() {
        parser.accept(x);
    }
    parser.flush_pending();
    SmtString::make(parser.string_so_far)
}

///
/// Check whether an integer is a valid SMT character
///
/// This checks whether integer `x` is less than or equal to [MAX_CHAR].
///
pub fn good_char(x: u32) -> bool {
    x <= MAX_CHAR
}

///
/// Check whether all elements in a slice are valid SMT characters
///
/// Return true if all integers in `a` are less than or equal to [MAX_CHAR].
///
pub fn good_string(a: &[u32]) -> bool {
    a.iter().all(|&x| x <= MAX_CHAR)
}

///
/// Convert an SMT character to a string literal
///
pub fn smt_char_as_string(x: u32) -> String {
    if x == '"' as u32 {
        "\"\"".to_string()
    } else if x >= 32 && x < 127 {
        char::from_u32(x).unwrap().to_string()
    } else if x < 32 || x == 127 {
        format!("\\u{{{:02x}}}", x)
    } else if x < 0x10000 {
        format!("\\u{:04x}", x)
    } else {
        format!("\\u{{{:x}}}", x)
    }
}

// Convert to an ASCII string in the SMT syntax
// - use escape sequences for non-printable ASCII characters and non-ASCII characters
// - convert "  to ""
impl fmt::Display for SmtString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;
        for &x in self.s.iter() {
            if x == '"' as u32 {
                write!(f, "\"\"")?;
            } else if x >= 32 && x < 127 {
                write!(f, "{}", char::from_u32(x).unwrap())?;
            } else if x < 32 || x == 127 {
                write!(f, "\\u{{{:02x}}}", x)?;
            } else if x < 0x10000 {
                write!(f, "\\u{:04x}", x)?;
            } else {
                write!(f, "\\u{{{:x}}}", x)?;
            }
        }
        write!(f, "\"")
    }
}

///
/// Convert integer x (interpreted as a Unicode codepoint) to a string in the SMT syntax:
///
/// 1) printable ASCII characters (other than double quote) are unchanged
/// 2) a double quote is converted to two double quotes
/// 3) non-printable ASCII characters are converted to "\u{xx}" (two hexadecimal digits)
/// 4) other characters are printed as "\uxxxx" or "\u{xxxxx}"
/// 5) if x is outside the valid SMT range (i.e., x > 0x2FFFF) then it's
///    converted to the non-SMT compliant string \u{xxxxxx} with as many hexadecimal
///    digits as required.
///
pub fn char_to_smt(x: u32) -> String {
    if x == '"' as u32 {
        "\"\"".to_string()
    } else if x >= 32 && x < 127 {
        char::from_u32(x).unwrap().to_string()
    } else if x < 32 || x == 127 {
        format!("\\u{{{:02x}}}", x)
    } else if x < 0x10000 {
        format!("\\u{:04x}", x)
    } else {
        format!("\\u{{{:x}}}", x)
    }
}

#[allow(dead_code)]
fn hex(i: u32) -> char {
    char::from_digit(i & 0xF, 16).unwrap()
}

#[allow(dead_code)]
fn append_smt_char(mut s: String, x: u32) -> String {
    if x == '"' as u32 {
        s.push_str("\"\"")
    } else if x >= 32 && x < 127 {
        s.push(char::from_u32(x).unwrap())
    } else if x < 32 {
        s.push_str("\\u{");
        s.push(hex(x >> 4));
        s.push(hex(x));
        s.push('}');
    } else if x < 0x10000 {
        s.push_str("\\u");
        s.push(hex(x >> 12));
        s.push(hex(x >> 8));
        s.push(hex(x >> 4));
        s.push(hex(x));
    } else {
        s.push_str("\\u{");
        s.push(hex(x >> 16));
        s.push(hex(x >> 12));
        s.push(hex(x >> 8));
        s.push(hex(x >> 4));
        s.push(hex(x));
        s.push('}');
    };
    s
}

// INTERNAL OPERATIONS ON VECTORS/SLICES

// Check whether all elements of v are valid code points
fn all_unicode(v: &[u32]) -> bool {
    v.iter().all(|&x| char::from_u32(x).is_some())
}

// Map to a regular string. If an element is not valid Unicode, it's replaced by U+FFFD
fn map_to_unicode(v: &[u32]) -> String {
    v.iter()
        .map(|&x| char::from_u32(x).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

// Check whether x is a decimal digit
fn char_is_digit(x: u32) -> bool {
    x >= '0' as u32 && x <= '9' as u32
}

// Check whether v < w in the lexicographic ordering
fn vector_lt(v: &[u32], w: &[u32]) -> bool {
    let max = cmp::min(v.len(), w.len());
    let mut i = 0;
    while i < max && v[i] == w[i] {
        i += 1;
    }
    if i == max {
        v.len() < w.len()
    } else {
        v[i] < w[i]
    }
}

// Check whether v <= w in the lexicographic ordering
fn vector_le(v: &[u32], w: &[u32]) -> bool {
    let max = cmp::min(v.len(), w.len());
    let mut i = 0;
    while i < max && v[i] == w[i] {
        i += 1;
    }
    if i == max {
        v.len() <= w.len()
    } else {
        v[i] < w[i]
    }
}

// Check whether v is a prefix of w
fn vector_prefix(v: &[u32], w: &[u32]) -> bool {
    let n = v.len();
    if n <= w.len() {
        let mut i = 0;
        while i < n && v[i] == w[i] {
            i += 1;
        }
        i == n
    } else {
        false // v is longer than w
    }
}

// Check whether v is a suffix of w
fn vector_suffix(v: &[u32], w: &[u32]) -> bool {
    let n = v.len();
    let m = w.len();
    if n <= m {
        let k = m - n;
        let mut i = 0;
        while i < n && v[i] == w[i + k] {
            i += 1;
        }
        i == n
    } else {
        false
    }
}

// Concatenate v and w
fn vector_concat(v: &[u32], w: &[u32]) -> Vec<u32> {
    let mut x = Vec::new();
    x.extend_from_slice(v);
    x.extend_from_slice(w);
    x
}

// find the first occurrence of v in w, starting at index i
fn find_sub_vector(v: &[u32], w: &[u32], i: usize) -> SearchResult {
    naive_search(v, w, i)
}

// SMT-LIKE FUNCTIONS ON STRINGS

///
/// Concatenate two strings
///
/// # Panics
///
/// If the resulting strings would have length larger than [MAX_LENGTH]
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("aa");
/// let s2 = SmtString::from("bb");
/// assert_eq!(str_concat(&s1,&s2), SmtString::from("aabb"));
/// ```
///
pub fn str_concat(s1: &SmtString, s2: &SmtString) -> SmtString {
    SmtString::make(vector_concat(&s1.s, &s2.s))
}

///
/// String length
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(str_len(&EMPTY), 0);
/// assert_eq!(str_len(&SmtString::from("abc")), 3);
/// ```
pub fn str_len(s: &SmtString) -> i32 {
    s.len() as i32
}

///
/// Character at index i in s, converted to a single-character string
///
/// - Characters are indexed from 0 to s.len - 1.
/// - Return the empty string if i is not in this range.
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s = SmtString::from("abcd");
///
/// assert_eq!(str_at(&s, 2), SmtString::from('c'));
/// assert_eq!(str_at(&s, 4), EMPTY);
/// ```
pub fn str_at(s: &SmtString, i: i32) -> SmtString {
    if i < 0 || i >= s.len() as i32 {
        EMPTY
    } else {
        SmtString::from(s.s[i as usize])
    }
}

///
/// Substring of s that starts at index i and has length at most n
///
/// - Return the empty string if n < 0 or i is not in [0 .. s.len-1]
/// - If s has length at least i+n, return the substring s[i...i+n-1]
/// - If s has length less than i+n, return the substring s[i .. s.len-1]
///
/// # Example
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s = SmtString::from("abcdef");
///
/// assert_eq!(str_substr(&s, 2, 3), SmtString::from("cde"));
/// ```
pub fn str_substr(s: &SmtString, i: i32, n: i32) -> SmtString {
    if i < 0 || i >= s.len() as i32 || n <= 0 {
        EMPTY
    } else {
        let i = i as usize;
        let n = n as usize;
        let j = cmp::min(i + n, s.s.len());
        SmtString::make_from_slice(s.s.get(i..j).unwrap())
    }
}

///
/// Strict lexicographic comparison.
///
/// - Return true if s1 < s2 in the lexicographic ordering
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("abcd");
/// let s3 = SmtString::from("bbb");
///
/// assert!(str_lt(&s2, &s1));
/// assert!(str_lt(&s1, &s3));
/// assert!(str_lt(&EMPTY, &s3));
///
/// assert!(! str_lt(&s1, &s2));
/// assert!(! str_lt(&s2, &s2));
/// assert!(! str_lt(&s2, &EMPTY));
/// ```
pub fn str_lt(s1: &SmtString, s2: &SmtString) -> bool {
    vector_lt(&s1.s, &s2.s)
}

///
/// Lexicographic comparison.
///
/// - Return true if s1 <= s2 in the lexicographic ordering
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("abcd");
/// let s3 = SmtString::from("bbb");
///
/// assert!(str_le(&s2, &s1));
/// assert!(str_le(&s1, &s3));
/// assert!(str_le(&s2, &s2));
/// assert!(str_le(&EMPTY, &s3));
///
/// assert!(! str_le(&s1, &s2));
/// assert!(! str_le(&s2, &EMPTY));
/// ```
pub fn str_le(s1: &SmtString, s2: &SmtString) -> bool {
    vector_le(&s1.s, &s2.s)
}

///
/// Check whether s1 is a prefix of s2
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("abcd");
/// let s3 = SmtString::from("bbb");
///
/// assert!(str_prefixof(&s2, &s1));
/// assert!(str_prefixof(&s1, &s1));
/// assert!(str_prefixof(&EMPTY, &s3));
///
/// assert!(! str_prefixof(&s1, &s2));
/// ```
pub fn str_prefixof(s1: &SmtString, s2: &SmtString) -> bool {
    vector_prefix(&s1.s, &s2.s)
}

///
/// Check whether s1 is a suffix of s2
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("def");
/// let s3 = SmtString::from("bbb");
///
/// assert!(str_suffixof(&s2, &s1));
/// assert!(str_suffixof(&s1, &s1));
/// assert!(str_suffixof(&EMPTY, &s3));
///
/// assert!(! str_suffixof(&s3, &s1));
/// ```
pub fn str_suffixof(s1: &SmtString, s2: &SmtString) -> bool {
    vector_suffix(&s1.s, &s2.s)
}

///
/// Check whether s2 is a substring of s1
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("cde");
/// let s3 = SmtString::from("cdd");
///
/// assert!(str_contains(&s1, &s2));;
/// assert!(str_contains(&s3, &EMPTY));
///
/// assert!(! str_contains(&s2, &s1));
/// assert!(! str_contains(&s1, &s3));
/// ```
pub fn str_contains(s1: &SmtString, s2: &SmtString) -> bool {
    match find_sub_vector(&s2.s, &s1.s, 0) {
        SearchResult::NotFound => false,
        SearchResult::Found(..) => true,
    }
}

///
/// Index of the first occurrence of s2 in s1, starting from index i
///
/// - If 0 <= i < s1.len and s2 occurs in s1[i ..] then return the index j >= i
///   of the first occurrence of s2 in s1[i ..].
/// - Return -1 if i < 0 or i >= s1.len or s2 does not occur in s1[i ..]
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("cde");
/// let s3 = SmtString::from("cdd");
///
/// assert_eq!(str_indexof(&s1, &s2, 0), 2);
/// assert_eq!(str_indexof(&s1, &s2, 2), 2);
/// assert_eq!(str_indexof(&s1, &s2, 3), -1);
/// assert_eq!(str_indexof(&s1, &s3, 0), -1);
/// ```
///
pub fn str_indexof(s1: &SmtString, s2: &SmtString, i: i32) -> i32 {
    if i < 0 || i >= s1.len() as i32 {
        -1
    } else {
        match find_sub_vector(&s2.s, &s1.s, i as usize) {
            SearchResult::NotFound => -1,
            SearchResult::Found(k, _) => k as i32,
        }
    }
}

///
/// Replace the first occurrence of p in s with r.
///
/// - Return s unchanged if p does not occur in s
///
/// # Panics
///
/// If the resulting string would have length larger than [MAX_LENGTH]
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdef");
/// let s2 = SmtString::from("cde");
/// let s3 = SmtString::from("Z");
///
/// assert_eq!(str_replace(&s1, &s2, &s3), SmtString::from("abZf"));
/// assert_eq!(str_replace(&s1, &EMPTY, &s3), SmtString::from("Zabcdef"));
/// ```
pub fn str_replace(s: &SmtString, p: &SmtString, r: &SmtString) -> SmtString {
    let s = &s.s;
    let p = &p.s;
    let r = &r.s;

    match find_sub_vector(p, s, 0) {
        SearchResult::NotFound => SmtString::make_from_slice(s),
        SearchResult::Found(i, j) => {
            let mut x = Vec::new();
            x.extend_from_slice(&s[..i]);
            x.extend_from_slice(r);
            x.extend_from_slice(&s[j..]);
            SmtString::make(x)
        }
    }
}

///
/// Replace all occurrences of p in s with r.
///
/// - return s unchanged if p is the empty string or if p doesn't occur in s
///
/// # Panics
///
/// If the resulting string would have length larger than [MAX_LENGTH]
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// let s1 = SmtString::from("abcdcdef");
/// let s2 = SmtString::from("cd");
/// let s3 = SmtString::from("Z");
///
/// assert_eq!(str_replace_all(&s1, &s2, &s3), SmtString::from("abZZef"));
/// assert_eq!(str_replace_all(&s1, &EMPTY, &s2), s1);
/// ```
pub fn str_replace_all(s: &SmtString, p: &SmtString, r: &SmtString) -> SmtString {
    if p.is_empty() {
        SmtString::make_from_slice(&s.s)
    } else {
        let s = &s.s;
        let p = &p.s;
        let r = &r.s;
        let mut x = Vec::new();
        let mut i = 0;
        while let SearchResult::Found(j, k) = find_sub_vector(p, s, i) {
            // s[j .. k] == p
            x.extend_from_slice(&s[i..j]);
            x.extend_from_slice(r);
            i = k;
        }
        x.extend_from_slice(&s[i..]);
        SmtString::make(x)
    }
}

///
/// Check whether s contains a single digit between '0' and '9'
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert!(str_is_digit(&SmtString::from("0")));
/// assert!(! str_is_digit(&SmtString::from("A")));
/// ```
pub fn str_is_digit(s: &SmtString) -> bool {
    s.len() == 1 && char_is_digit(s.s[0])
}

///
/// Code for s if s is a single-character string, -1 otherwise
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(str_to_code(&EMPTY), -1);
/// assert_eq!(str_to_code(&SmtString::from(1202)), 1202);
/// assert_eq!(str_to_code(&SmtString::from("abc")), -1);
/// ```
pub fn str_to_code(s: &SmtString) -> i32 {
    if s.len() == 1 {
        s.s[0] as i32
    } else {
        -1
    }
}

///
/// Single-character string with character code x
///
/// - Return a single-character string if 0 <= x <= 0x2ffff
/// - Return the empty string otherwise
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(str_from_code(-19), EMPTY);
/// assert_eq!(str_from_code(1202), SmtString::from(1202));
/// assert_eq!(str_from_code(0x30000), EMPTY);
/// ```
pub fn str_from_code(x: i32) -> SmtString {
    if 0 <= x && x <= MAX_CHAR as i32 {
        SmtString::from(x as u32)
    } else {
        EMPTY
    }
}

///
/// Convert s to an integer
///
/// - Return a non-negative integer if s consists entirely of decimal digits.
/// - Return -1 otherwise
///
/// # Panics
///
/// If the result is too large and does not fit in `i32`.
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(str_to_int(&SmtString::from("00982")), 982);
/// assert_eq!(str_to_int(&EMPTY), -1);
/// assert_eq!(str_to_int(&SmtString::from("101aaabb")), -1);
/// ```
pub fn str_to_int(s: &SmtString) -> i32 {
    if s.is_empty() {
        return -1;
    }

    let mut x: i32 = 0;
    for &d in &s.s {
        if char_is_digit(d) {
            let y = 10 * x + (d as i32 - '0' as i32);
            if y < x {
                panic!("Arithmetic overflow in str_to_int");
            }
            x = y;
        } else {
            return -1;
        }
    }
    x
}

///
/// Convert x to a string
///
/// - Return a sequence of digits if x >= 0
/// - Return the empty string if x < 0
///
/// # Examples
/// ```
/// use amzn_smt_strings::smt_strings::*;
///
/// assert_eq!(str_from_int(0), SmtString::from("0"));
/// assert_eq!(str_from_int(-1), EMPTY);
/// assert_eq!(str_from_int(1002), SmtString::from("1002"));
/// ```
pub fn str_from_int(x: i32) -> SmtString {
    if x >= 0 {
        SmtString::from(x.to_string())
    } else {
        EMPTY
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constructors() {
        assert_eq!(EMPTY, "".into());
        assert_eq!(SmtString::from("ABCD"), SmtString::from(&[65, 66, 67, 68]));
        assert_eq!(
            SmtString::from("AB\u{12ff}D"),
            SmtString::from(&[65, 66, 0x12FF, 68])
        );
        assert_eq!(SmtString::from(0x1300), SmtString::from(&[0x1300u32]));
        assert_eq!(SmtString::from(0x30000), SmtString::from(&[0xFFFD]));
        assert_eq!(SmtString::from('K'), SmtString::from(&[75]));
        assert_eq!(
            SmtString::from(&[0x0, 0x100, 0x2FFFF, 0x30000, 0x40000]),
            SmtString::from(&[0, 256, 0x2FFFF, 0xFFFD, 0xFFFD])
        );
    }

    #[test]
    fn test_parsing() {
        assert_eq!(parse_smt_literal(""), EMPTY);
        assert_eq!(
            parse_smt_literal("A\"BB"),
            SmtString::from(&[65, 34, 66, 66])
        );
        assert_eq!(
            parse_smt_literal("abcd"),
            SmtString::from(&[97, 98, 99, 100])
        );
        assert_eq!(parse_smt_literal(r"\u{1aB6e}"), SmtString::from(0x1AB6E));

        assert_eq!(
            parse_smt_literal(r"\u2CA"),
            SmtString::from(&[92, 117, 50, 67, 65])
        );
        assert_eq!(
            parse_smt_literal(r"\u{ACG}A"),
            SmtString::from(&[92, 117, 123, 65, 67, 71, 125, 65])
        );
        assert_eq!(
            parse_smt_literal(r"\u{}"),
            SmtString::from(&[92, 117, 123, 125])
        );
        assert_eq!(
            parse_smt_literal(r"\u{3ffff}"),
            SmtString::from(&[92, 117, 123, 51, 102, 102, 102, 102, 125])
        );
        assert_eq!(
            parse_smt_literal(r"\u{\u{09}"),
            SmtString::from(&[92, 117, 123, 9])
        );
        assert_eq!(
            parse_smt_literal(r"\u\u{09}"),
            SmtString::from(&[92, 117, 9])
        );
        assert_eq!(parse_smt_literal(r"\\u{09}"), SmtString::from(&[92, 9]));
    }

    #[test]
    fn test_format() {
        assert_eq!(EMPTY.to_string(), r#""""#);
        assert_eq!(SmtString::from(&[65, 34, 66]).to_string(), r#""A""B""#);
        assert_eq!(SmtString::from("abcd").to_string(), r#""abcd""#);
        assert_eq!(
            parse_smt_literal(r"\u{1aB6e}").to_string(),
            r#""\u{1ab6e}""#
        );
        assert_eq!(parse_smt_literal(r"\u{12DD}").to_string(), r#""\u12dd""#);
        assert_eq!(SmtString::from(0).to_string(), r#""\u{00}""#);
    }

    #[test]
    fn test_concat() {
        let s1 = SmtString::from("abcd");
        let s2 = SmtString::from("efg");
        assert_eq!(str_concat(&s1, &s2), SmtString::from("abcdefg"));
        assert_eq!(str_concat(&s1, &EMPTY), s1);
        assert_eq!(str_concat(&EMPTY, &s2), s2);
        assert_eq!(str_concat(&EMPTY, &EMPTY), EMPTY);
    }

    #[test]
    fn test_length() {
        let s1 = SmtString::from("abcd");
        let s2 = SmtString::from("\u{01dd}");
        assert_eq!(str_len(&s1), 4);
        assert_eq!(str_len(&s2), 1);
        assert_eq!(str_len(&EMPTY), 0);
    }

    #[test]
    fn test_at() {
        let s = SmtString::from("abcde");
        assert_eq!(str_at(&s, 0), SmtString::from('a'));
        assert_eq!(str_at(&s, 2), SmtString::from('c'));
        assert_eq!(str_at(&s, 4), SmtString::from('e'));
        assert_eq!(str_at(&s, 5), EMPTY);
        assert_eq!(str_at(&s, -1), EMPTY);
        assert_eq!(str_at(&EMPTY, 0), EMPTY);
    }

    #[test]
    fn test_substr() {
        let s = SmtString::from("abcdef");
        assert_eq!(str_substr(&s, 2, 3), SmtString::from("cde"));
        assert_eq!(str_substr(&s, 0, str_len(&s)), s);
        assert_eq!(str_substr(&s, 2, 10), SmtString::from("cdef"));
        assert_eq!(str_substr(&s, 2, 0), EMPTY);
        assert_eq!(str_substr(&s, 6, 4), EMPTY);
    }

    #[test]
    fn test_lexorder() {
        let s1 = SmtString::from("abcdef");
        let s2 = SmtString::from("abcd");
        let s3 = SmtString::from("bbb");

        assert!(str_lt(&s2, &s1));
        assert!(str_lt(&s1, &s3));
        assert!(str_lt(&EMPTY, &s3));

        assert!(!str_lt(&s1, &s2));
        assert!(!str_lt(&s2, &s2));
        assert!(!str_lt(&s2, &EMPTY));
        assert!(!str_lt(&EMPTY, &EMPTY));

        assert!(str_le(&s2, &s1));
        assert!(str_le(&s1, &s3));
        assert!(str_le(&s2, &s2));
        assert!(str_le(&EMPTY, &s3));
        assert!(str_le(&EMPTY, &EMPTY));

        assert!(!str_le(&s1, &s2));
        assert!(!str_le(&s2, &EMPTY));
    }

    #[test]
    fn test_substrings() {
        let s1 = SmtString::from("abcdef");
        let s2 = SmtString::from("abcd");
        let s3 = SmtString::from("bbb");
        let s4 = SmtString::from("def");
        let s5 = SmtString::from("bc");

        assert!(str_prefixof(&s2, &s1));
        assert!(str_prefixof(&s1, &s1));
        assert!(str_prefixof(&EMPTY, &s3));
        assert!(str_prefixof(&EMPTY, &EMPTY));

        assert!(!str_prefixof(&s1, &s2));
        assert!(!str_prefixof(&s3, &s1));
        assert!(!str_prefixof(&s1, &EMPTY));
        assert!(!str_prefixof(&s5, &s1));

        assert!(str_suffixof(&s4, &s1));
        assert!(str_suffixof(&s1, &s1));
        assert!(str_suffixof(&EMPTY, &s3));
        assert!(str_suffixof(&EMPTY, &EMPTY));

        assert!(!str_suffixof(&s1, &s2));
        assert!(!str_suffixof(&s3, &s1));
        assert!(!str_suffixof(&s1, &EMPTY));
        assert!(!str_suffixof(&s5, &s1));

        assert!(str_contains(&s1, &s2));
        assert!(str_contains(&s1, &s1));
        assert!(str_contains(&s1, &s4));
        assert!(str_contains(&s1, &s5));
        assert!(str_contains(&s3, &EMPTY));
        assert!(str_contains(&EMPTY, &EMPTY));

        assert!(!str_contains(&s2, &s1));
        assert!(!str_contains(&s1, &s3));
        assert!(!str_contains(&EMPTY, &s1));
    }

    #[test]
    fn test_indexof() {
        let s1 = SmtString::from("abcdef");
        let s2 = SmtString::from("cde");
        let s3 = SmtString::from("cdd");

        assert_eq!(str_indexof(&s1, &s2, 0), 2);
        assert_eq!(str_indexof(&s1, &s2, 2), 2);
        assert_eq!(str_indexof(&s1, &s2, 3), -1);
        assert_eq!(str_indexof(&s1, &s1, 0), 0);
        assert_eq!(str_indexof(&s1, &EMPTY, 4), 4);
        assert_eq!(str_indexof(&s1, &s3, 0), -1);
        assert_eq!(str_indexof(&s1, &s2, -10), -1);
        assert_eq!(str_indexof(&s1, &s1, 1), -1);
        assert_eq!(str_indexof(&EMPTY, &s1, 2), -1);
    }

    #[test]
    fn test_replace() {
        let s1 = SmtString::from("abcdef");
        let s2 = SmtString::from("cde");
        let s3 = SmtString::from("Z");
        let s4 = SmtString::from("VWXYZ");

        assert_eq!(str_replace(&s1, &s2, &s3), SmtString::from("abZf"));
        assert_eq!(str_replace(&s1, &s2, &s4), SmtString::from("abVWXYZf"));
        assert_eq!(str_replace(&s1, &s2, &s2), s1);
        assert_eq!(str_replace(&s1, &s3, &s4), s1);
        assert_eq!(str_replace(&s1, &EMPTY, &s3), SmtString::from("Zabcdef"));
        assert_eq!(str_replace(&s4, &s3, &EMPTY), SmtString::from("VWXY"));
    }

    #[test]
    fn test_replace_all() {
        let s1 = SmtString::from("abcdcdef");
        let s2 = SmtString::from("cd");
        let s3 = SmtString::from("Z");
        let s4 = SmtString::from("VWX");
        let s5 = SmtString::from("f");

        assert_eq!(str_replace_all(&s1, &s2, &s3), "abZZef".into());
        assert_eq!(str_replace_all(&s1, &s2, &s4), "abVWXVWXef".into());
        assert_eq!(str_replace_all(&s1, &EMPTY, &s2), s1);
        assert_eq!(str_replace_all(&s1, &s3, &s4), s1);
        assert_eq!(str_replace_all(&s1, &s2, &EMPTY), "abef".into());
        assert_eq!(str_replace_all(&s1, &s5, &s2), "abcdcdecd".into());
    }

    #[test]
    fn test_is_digit() {
        assert!(str_is_digit(&SmtString::from("0")));
        assert!(str_is_digit(&SmtString::from('5')));
        assert!(str_is_digit(&SmtString::from("9")));
        assert!(!str_is_digit(&SmtString::from("10")));
        assert!(!str_is_digit(&EMPTY));
        assert!(!str_is_digit(&SmtString::from("A")));
    }

    #[test]
    fn test_code() {
        assert_eq!(str_to_code(&EMPTY), -1);
        assert_eq!(str_to_code(&SmtString::from(1202)), 1202);
        assert_eq!(str_to_code(&SmtString::from("abc")), -1);

        assert_eq!(str_from_code(-19), EMPTY);
        assert_eq!(str_from_code(1202), SmtString::from(1202));
        assert_eq!(str_from_code(0x30000), EMPTY);
    }

    #[test]
    fn test_int() {
        assert_eq!(str_to_int(&SmtString::from("00982")), 982);
        assert_eq!(str_to_int(&EMPTY), -1);
        assert_eq!(str_to_int(&SmtString::from("101aaabb")), -1);

        assert_eq!(str_from_int(0), SmtString::from("0"));
        assert_eq!(str_from_int(-1), EMPTY);
        assert_eq!(str_from_int(1002), SmtString::from("1002"));
    }
}
