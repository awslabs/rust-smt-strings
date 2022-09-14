// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Regular expressions
//!
//! This module defines the abstract syntax of regular expressions [BaseRegLan]
//! and the regular expression type [RE]. Regular expressions are built using
//! an [ReManager], which provides hash consing.
//!
//! Input to the manager's methods are static references to [RE] objects
//! (see type [RegLan]). The manager also returns objects of type [RegLan]
//! when producing regular expressions.
//!
//! [ReManager] also implements the *derivative* operation. The derivative of a regular
//! expression R with respect to a character c is another regular expression S that
//! defines all the strings that can follow c in the language of R. For example,
//! the derivative of regular expression '(abc + cd)\*' with respect to 'a'  is
//! 'bc(abc + cd)\*': all words of '(abc + cd)\*' that start with 'a' are of the
//! form 'a.w' where 'w' is a word 'bc(abc + cd)\*'.
//!
//! For a regular expression R, we use a [CharPartition] that divides the alphabet into
//! equivalent *derivative classes*. If two characters `c1` and `c2` are in the same
//! derivative class, then the derivative of R with respect to `c1` and the derivative of R
//! with respect to `c2` are equal. The [ReManager] implements derivative of R with respect
//! to one of its derivative class. More generally, the derivative of R with respect to a
//! character set C is well defined if C is included in a derivative class of R.
//!
//! Derivatives allows one to convert REs to deterministic automata and support
//! other operations such as checking whether a string matches an RE.
//!

use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;

use crate::automata::Automaton;
use crate::automata::AutomatonBuilder;
use crate::bfs_queues::*;
use crate::character_sets::*;
use crate::errors::*;
use crate::labeled_queues::LabeledQueue;
use crate::loop_ranges::*;
use crate::matcher::SearchResult;
use crate::smt_strings::SmtString;
use crate::smt_strings::MAX_CHAR;
use crate::store::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
///
/// Abstract syntax for regular expressions
///
pub enum BaseRegLan {
    /// Empty language
    Empty,

    /// The language that contains only the empty string
    Epsilon,

    /// Words of length one with characters is a range [a, b]
    Range(CharSet),

    /// Concatenation of two languages
    Concat(RegLan, RegLan),

    /// Generalized loop: see [loop_ranges][crate::loop_ranges]
    Loop(RegLan, LoopRange),

    /// Complement of a language
    Complement(RegLan),

    /// Union of two or more languages
    Union(Box<[RegLan]>),

    /// Intersection of two or more languages
    Inter(Box<[RegLan]>),
}

/// Reference to a Regular Expression descriptor
pub type RegLan = &'static RE;

///
/// Regular expression structure
///
/// A regular expression includes an expression of type [BaseRegLan],
/// which is an abstract syntax tree.
///
/// In addition, each regular expression e has a
/// unique integer id and three attributes:
/// - e.nullable is true if the language of e contains the empty string
/// - e.singleton is true if the language of e contains a single string
/// - e.deriv_class is the list of derivative classes of e.
///
/// The derivative classes are disjoint interval characters that cover
/// a subset of the alphabet, and a complementary class that covers the rest.
/// See [CharPartition][crate::character_sets::CharPartition]. The `deriv_class` partition is
/// constructed to ensure that all the characters in a class produce the same
/// derivative of e: if c1 and c2 are in the same derivative class of e then
/// deriv(e, c1) and deriv(e, c2) are equal.
///
/// Operations on regular expressions use hash-consing and are performed with
/// an [ReManager].
#[derive(Debug)]
pub struct RE {
    /// Abstract syntax tree
    expr: BaseRegLan,
    /// Unique id for this RE
    id: usize,
    /// Whether the language contains the empty string
    pub nullable: bool,
    /// Whether this RE has a single element
    singleton: bool,
    /// Whether this RE is a simple pattern, i.e.,
    /// a concatenation of Loops and Ranges
    simple_pattern: bool,
    /// Partition of character sets relevant to this RE
    deriv_class: Rc<CharPartition>,
}

/// Equality on RE is derived from the unique ids.
///
/// Two REs are equal iff they have the same id.
impl PartialEq for RE {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for RE {}

/// Ordering on REs is based on unique ids.
///
/// We have re1 < re2 iff re1.id < re2.id
impl PartialOrd for RE {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl Ord for RE {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

/// The hash code of a RE is just the hash code of its id.
impl Hash for RE {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

// utility: add n copies of x to vector v
fn push_multiple<T: Copy>(v: &mut Vec<T>, n: u32, x: T) {
    for _ in 0..n {
        v.push(x);
    }
}

impl BaseRegLan {
    /// Check whether the empty word is in this language
    fn is_nullable(&self) -> bool {
        match self {
            BaseRegLan::Empty => false,
            BaseRegLan::Epsilon => true,
            BaseRegLan::Range(_) => false,
            BaseRegLan::Concat(e1, e2) => e1.nullable && e2.nullable,
            BaseRegLan::Loop(e, range) => range.start() == 0 || e.nullable,
            BaseRegLan::Complement(e) => !e.nullable,
            BaseRegLan::Inter(args) => args.iter().all(|x| x.nullable),
            BaseRegLan::Union(args) => args.iter().any(|x| x.nullable),
        }
    }

    /// Check whether this RE is atomic (either Empty, Epsilon, or a character Range)
    pub fn is_atomic(&self) -> bool {
        matches!(
            self,
            BaseRegLan::Empty | BaseRegLan::Epsilon | BaseRegLan::Range(_)
        )
    }

    /// Check whether this RE is Concat/Loop or Atomic
    fn concat_or_atomic(&self) -> bool {
        matches!(
            self,
            BaseRegLan::Empty
                | BaseRegLan::Epsilon
                | BaseRegLan::Range(..)
                | BaseRegLan::Concat(..)
                | BaseRegLan::Loop(..)
        )
    }

    /// Check whether this RE is sigma (all chars)
    fn is_all_chars(&self) -> bool {
        if let BaseRegLan::Range(s) = self {
            s.is_alphabet()
        } else {
            false
        }
    }

    /// Check whether this RE is sigma^* (full language)
    fn is_full(&self) -> bool {
        if let BaseRegLan::Loop(r, range) = self {
            range.is_all() && r.expr.is_all_chars()
        } else {
            false
        }
    }

    /// Check whether this regular expression is of the form (str.to_re <some string>)
    /// This holds if the RE is epsilon or if it's a concatenation of characters
    fn is_singleton(&self) -> bool {
        match self {
            BaseRegLan::Epsilon => true,
            BaseRegLan::Range(c) => c.is_singleton(),
            BaseRegLan::Concat(e1, e2) => e1.singleton && e2.singleton,
            BaseRegLan::Loop(e, range) => e.singleton && range.is_point(),
            _ => false,
        }
    }

    /// Check whether this regular expression is a concatenation of ranges
    /// and loops over ranges.
    fn is_simple_pattern(&self) -> bool {
        match self {
            BaseRegLan::Epsilon => true,
            BaseRegLan::Range(..) => true,
            BaseRegLan::Loop(r, ..) => matches!(r.expr, BaseRegLan::Range(..)),
            BaseRegLan::Concat(e1, e2) => e1.simple_pattern && e2.simple_pattern,
            _ => false,
        }
    }

    /// Check whether this regular expression a Range
    /// (i.e., an interval of characters [c0, c1])
    fn is_range(&self) -> bool {
        matches!(self, BaseRegLan::Range(..))
    }

    /// Check whether all strings of `self` are one-character long and belong to s
    fn match_char_set(&self, s: &CharSet) -> bool {
        match self {
            BaseRegLan::Range(x) => s.covers(x),
            _ => false,
        }
    }

    /// Compute the derivation classes for this regular expression
    fn deriv_class(&self) -> Rc<CharPartition> {
        fn rc(p: CharPartition) -> Rc<CharPartition> {
            Rc::new(p)
        }

        fn merge_deriv_classes(a: &[RegLan]) -> Rc<CharPartition> {
            let mut result = CharPartition::new();
            for &re in a {
                result = merge_partitions(&result, &re.deriv_class)
            }
            rc(result)
        }

        fn empty_partition() -> Rc<CharPartition> {
            rc(CharPartition::new())
        }

        match self {
            BaseRegLan::Empty => empty_partition(),
            BaseRegLan::Epsilon => empty_partition(),
            BaseRegLan::Range(c) => rc(CharPartition::from_set(c)),
            BaseRegLan::Concat(e1, e2) => {
                if e1.nullable {
                    rc(merge_partitions(&e1.deriv_class, &e2.deriv_class))
                } else {
                    e1.deriv_class.clone()
                }
            }
            BaseRegLan::Loop(e, _) => e.deriv_class.clone(),
            BaseRegLan::Complement(e) => e.deriv_class.clone(),
            BaseRegLan::Inter(args) => merge_deriv_classes(args.as_ref()),
            BaseRegLan::Union(args) => merge_deriv_classes(args.as_ref()),
        }
    }

    /// Collect all characters of this RE (if it's a singleton)
    #[allow(dead_code)]
    fn collect_chars(&self, v: &mut Vec<u32>) {
        match self {
            BaseRegLan::Range(c) => {
                if c.is_singleton() {
                    v.push(c.pick());
                }
            }
            BaseRegLan::Loop(r, range) => {
                if range.is_point() {
                    if let BaseRegLan::Range(c) = r.expr {
                        if c.is_singleton() {
                            push_multiple(v, range.start(), c.pick());
                        }
                    }
                }
            }
            BaseRegLan::Concat(e1, e2) => {
                e1.expr.collect_chars(v);
                e2.expr.collect_chars(v);
            }
            _ => (),
        }
    }
}

impl HashConsed for RE {
    type Key = BaseRegLan;

    fn make(index: usize, k: &Self::Key) -> Self {
        RE {
            expr: k.clone(),
            id: index,
            nullable: k.is_nullable(),
            singleton: k.is_singleton(),
            simple_pattern: k.is_simple_pattern(),
            deriv_class: k.deriv_class(),
        }
    }
}

impl Display for BaseRegLan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // write either e or '(e)' when e is a sub-expression
        fn write_sub(f: &mut std::fmt::Formatter<'_>, e: RegLan) -> std::fmt::Result {
            if e.singleton || e.expr.is_atomic() {
                write!(f, "{}", e.expr)
            } else {
                write!(f, "({})", e.expr)
            }
        }

        // write a list of operands separated by an symbol
        fn write_list(
            f: &mut std::fmt::Formatter<'_>,
            l: &[RegLan],
            symbol: char,
        ) -> std::fmt::Result {
            debug_assert!(!l.is_empty());
            write_sub(f, l[0])?;
            for e in &l[1..] {
                write!(f, " {} ", symbol)?;
                write_sub(f, e)?;
            }
            Ok(())
        }

        match self {
            BaseRegLan::Empty => write!(f, "\u{2205}"), // empty set
            BaseRegLan::Epsilon => write!(f, "\u{03B5}"),
            BaseRegLan::Range(r) => write!(f, "{}", r),
            BaseRegLan::Concat(e1, e2) => {
                let mut v = Vec::new();
                flatten_concat(e1, &mut v);
                flatten_concat(e2, &mut v);
                for e in v {
                    write_sub(f, e)?
                }
                Ok(())
            }
            BaseRegLan::Loop(e, range) => {
                write_sub(f, e)?;
                write!(f, "^{}", range)
            }
            BaseRegLan::Complement(e) => {
                write!(f, "\u{00AC}")?;
                write_sub(f, e)
            }
            BaseRegLan::Inter(args) => write_list(f, args, '&'),
            BaseRegLan::Union(args) => write_list(f, args, '+'),
        }
    }
}

impl Display for RE {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.expr.fmt(f)
    }
}

impl RE {
    /// check whether the complementary class is empty
    pub fn empty_complement(&self) -> bool {
        self.deriv_class.empty_complement()
    }

    /// number of derivative classes (not including the complementary class)
    pub fn num_deriv_classes(&self) -> usize {
        self.deriv_class.len()
    }

    /// check whether cid is a valid class id
    pub fn valid_class_id(&self, cid: ClassId) -> bool {
        self.deriv_class.valid_class_id(cid)
    }

    /// Check whether this RE is equal to the empty RE
    pub fn is_empty(&self) -> bool {
        matches!(self.expr, BaseRegLan::Empty)
    }

    /// pick a representative element in a derivative class
    ///
    /// - if cid is Interval(i): pick in class i
    /// - if cid is Complement: pick in the complementary class
    ///
    fn pick_class_rep(&self, cid: ClassId) -> u32 {
        self.deriv_class.pick_in_class(cid)
    }

    /// class of point x
    fn class_of_char(&self, x: u32) -> ClassId {
        debug_assert!(x <= MAX_CHAR);
        self.deriv_class.class_of_char(x)
    }

    /// class of set s
    fn class_of_set(&self, s: &CharSet) -> Result<ClassId, Error> {
        self.deriv_class.class_of_set(s)
    }

    /// iterator to go through valid classIds
    pub fn class_ids(&self) -> ClassIdIterator<'_> {
        self.deriv_class.class_ids()
    }

    /// iterator to go through the intervals in an RE derivative classes
    pub fn char_ranges(&self) -> impl Iterator<Item = &CharSet> {
        self.deriv_class.ranges()
    }

    /// incomplete check for inclusion
    /// - if this returns true then self is included in other
    /// - otherwise, we don't know
    pub fn included_in(&self, other: &Self) -> bool {
        sub_language(self, other)
    }
}

/// Iterator to go through all sub-terms of a RegLan
/// We can't implement this in RE because of lifetime issues
#[derive(Debug)]
struct ReIterator {
    queue: BfsQueue<RegLan>,
}

impl Iterator for ReIterator {
    type Item = RegLan;

    /// List all sub-terms in breadth-first order, without duplicates
    fn next(&mut self) -> Option<Self::Item> {
        fn get_next(queue: &mut BfsQueue<RegLan>) -> Option<RegLan> {
            if queue.is_empty() {
                None
            } else {
                let x = queue.pop().unwrap();
                match x.expr {
                    BaseRegLan::Concat(left, right) => {
                        queue.push(left);
                        queue.push(right);
                    }
                    BaseRegLan::Loop(x, _) => {
                        queue.push(x);
                    }
                    BaseRegLan::Complement(x) => {
                        queue.push(x);
                    }
                    BaseRegLan::Inter(ref list) => {
                        queue.push_all(list.iter().copied());
                    }
                    BaseRegLan::Union(ref list) => {
                        queue.push_all(list.iter().copied());
                    }
                    _ => (),
                }
                Some(x)
            }
        }

        get_next(&mut self.queue)
    }
}

///
/// Iterator for the sub-terms of r
/// - This enumerates the sub-terms of r, without duplicates,
///   in a breadth-first order. The term r is included.
///   It comes first in the iteration.
///
pub fn sub_terms(r: RegLan) -> impl Iterator<Item = RegLan> {
    let mut queue = BfsQueue::new();
    queue.push(r);
    ReIterator { queue }
}

///
/// Iterator that enumerates the leaves of r
/// - A leaf is an atomic sub-term of r (i.e., a term t such that f.expr is either
///   [BaseRegLan::Empty], or [BaseRegLan::Epsilon] or [BaseRegLan::Range])
/// - All leaves are listed once (no duplicates)
/// - If r itself is atomic, the iterator just produces r and nothing else.
///  
pub fn leaves(r: RegLan) -> impl Iterator<Item = RegLan> {
    sub_terms(r).filter(|&x| x.expr.is_atomic())
}

///
/// Collect a list L = (R_1,...R_n) such that r = concat(R_1,...,R_n)
/// and no R_i is itself of the form concat(...) or epsilon, then
/// add the R_is to vector v.
///
fn flatten_concat<'a>(r: &'a RE, v: &mut Vec<&'a RE>) {
    match &r.expr {
        BaseRegLan::Epsilon => (), // skip epsilon
        BaseRegLan::Concat(x, y) => {
            flatten_concat(x, v);
            flatten_concat(y, v)
        }
        _ => v.push(r),
    }
}

///
/// Same as flatten concat but return a vector of R_1, ..., R_n
///
fn decompose_concat(r: &RE) -> Vec<&RE> {
    let mut result = Vec::new();
    flatten_concat(r, &mut result);
    result
}

///
/// collect a list L= {R_1, ..., R_n} of languages such
/// that R = inter(R_1, ..., R_n) and no R_i is itself of the form inter(...)
/// add R_1 ... R_n to v
///
fn flatten_inter<'a>(r: &'a RE, v: &mut Vec<&'a RE>) {
    match &r.expr {
        BaseRegLan::Inter(x) => {
            for &s in x.as_ref() {
                flatten_inter(s, v)
            }
        }
        _ => v.push(r),
    }
}

///
/// collect a list L= {R_1, ..., R_n} of languages such
/// that R = union(R_1, ..., R_n) and no R_i is itself of the form union(...)
/// add R_1 ... R_n to v
///
fn flatten_union<'a>(r: &'a RE, v: &mut Vec<&'a RE>) {
    match &r.expr {
        BaseRegLan::Union(x) => {
            for &s in x.as_ref() {
                flatten_union(s, v)
            }
        }
        _ => v.push(r),
    }
}

/// check whether a sorted slice v contains x
/// this is used for x=empty or x=full or x=epsilon, which have small ids,
/// so if x occurs, that will be at the beginning of v.
fn contains<'a>(v: &[&'a RE], x: &'a RE) -> bool {
    for &y in v {
        if *y == *x {
            return true;
        }
        if *y > *x {
            return false;
        }
    }
    false
}

/// reset a then store x as its unique element
fn set_to_singleton<'a>(a: &mut Vec<&'a RE>, x: &'a RE) {
    a.clear();
    a.push(x);
}

///
/// Subsumption/Language inclusion
///
/// A regular expression R subsumes another regular expression S is
/// the language of S is included in the language of R. We try to
/// detect subsumptions to simplify unions and intersections
/// of regular expressions.
///
/// We do this when R is a simple pattern, that is, a concatenation
/// of Range and Loop REs. In this case, we can write R as a concatenation
/// of basic patterns. Each base pattern is either a sequence of Range
/// expressions or a sequence of loop expressions. We say that a sequence
/// of Range expression is a rigid pattern (e.g., it can be something like a string
/// 'abc'). A sequence of loop expression is a flexible pattern (e.g., something like
/// Sigma^*).
///
/// To check whether R subsumes S:
/// - construct the list of basic patterns of R
/// - first pass: find matches in S for all the rigid patterns of R. Each match is a slice of S
///   say S[i, j]
/// - second pass: the parts of S that are not matched in the first pass must now match
///   flexible patterns of R in sequence.
///

/// Data structure to represent a basic pattern of array R of RegLan
/// - start and end are indices in R such that start < end
/// - this means that R[start, end-1] is a base pattern
/// - if we find a match for R in an array S, we set
///   start_match and end_match to mean that S[start_match, end_match-1]
///   matches the base_pattern. We must have start_match <= end_match.
///
#[derive(Debug)]
struct BasePattern {
    start: usize,
    end: usize,
    is_rigid: bool,
    start_match: usize,
    end_match: usize,
}

impl BasePattern {
    fn len(&self) -> usize {
        self.end - self.start
    }

    fn set_match(&mut self, start: usize, end: usize) {
        self.start_match = start;
        self.end_match = end;
    }

    fn make(start: usize, end: usize, is_rigid: bool) -> BasePattern {
        debug_assert!(start < end);
        BasePattern {
            start,
            end,
            is_rigid,
            start_match: 0,
            end_match: 0,
        }
    }
}

impl Display for BasePattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let k = if self.is_rigid { "Rigid" } else { "Flex" };
        write!(f, "{}({}, {})", k, self.start, self.end)
    }
}

/// Construct a vector of base patterns from a slice of RegLan
fn base_patterns(r: &[&RE]) -> Vec<BasePattern> {
    let mut result = Vec::new();
    if !r.is_empty() {
        let mut j = 0;
        let mut rigid_slice = r[0].expr.is_range();
        for (i, re) in r.iter().enumerate().skip(1) {
            let rigid_i = re.expr.is_range();
            if rigid_slice != rigid_i {
                result.push(BasePattern::make(j, i, rigid_slice));
                rigid_slice = rigid_i;
                j = i;
            }
        }
        // last base_pattern
        result.push(BasePattern::make(j, r.len(), rigid_slice))
    }
    result
}

/// Check whether s[i..pattern.len()-1] matches pattern
/// Requires i + pattern.len() <= s.lend()
fn rigid_match_at<'a>(pattern: &[&CharSet], s: &[&'a RE], i: usize) -> bool {
    debug_assert!(i + pattern.len() <= s.len());
    for j in 0..pattern.len() {
        if !s[i + j].expr.match_char_set(pattern[j]) {
            return false;
        }
    }
    true
}

/// Search for a match of pattern in sequence s, starting at index i
/// `pattern` is a rigid pattern represented as a sequence of CharSets
fn next_rigid_match<'a>(pattern: &[&CharSet], s: &[&'a RE], i: usize) -> SearchResult {
    let p_len = pattern.len();
    let s_len = s.len();
    if s_len >= p_len {
        for j in i..(s_len - p_len) {
            if rigid_match_at(pattern, s, j) {
                return SearchResult::Found(j, j + p_len);
            }
        }
    }
    SearchResult::NotFound
}

/// Search for a match of pattern in sequence s, starting from index i and going down
/// `pattern` is a rigid pattern represented as a sequence of CharSets
fn prev_rigid_match<'a>(pattern: &[&CharSet], s: &[&'a RE], i: usize) -> SearchResult {
    let p_len = pattern.len();
    for j in (p_len..=i).rev() {
        if rigid_match_at(pattern, s, j - p_len) {
            return SearchResult::Found(j - p_len, j);
        }
    }
    SearchResult::NotFound
}

/// Collect the list of CharSets from a rigid pattern
/// the pattern `p` is given as a list of regular expressions.
/// each regular expression in `p` is assumed to be character Range.
fn char_sets_of_pattern<'a>(p: &[&'a RE]) -> Vec<&'a CharSet> {
    let mut result = Vec::new();
    for r in p {
        if let BaseRegLan::Range(s) = &r.expr {
            result.push(s)
        } else {
            panic!()
        }
    }
    result
}

/// Check whether a concatenation of REs starts with a rigid pattern
/// - 'u' is a sequence of REs (concatenated)
/// - 'v' and 'p' define the pattern to search for:
///    `p` identifies a slice of 'v' (from p.start to p.end)
///    this slice is a concatenation of Range expressions
/// - return true if 'u' starts with a sequence of Range expressions
///   of the same length as the pattern and that each range expression in `u` is
///   included in the corresponding range expression in the pattern.
fn rigid_prefix_match<'a>(u: &[&'a RE], v: &[&'a RE], p: &BasePattern) -> bool {
    if u.len() >= p.len() {
        let p = char_sets_of_pattern(&v[p.start..p.end]);
        rigid_match_at(&p, u, 0)
    } else {
        false
    }
}

/// Check whether a concatenation of REs end with a rigid pattern
/// - 'u' is a sequence of REs
/// - 'v' and 'p' define the pattern to search for
/// - return true if 'u' ends with a sequence of REs that match this pattern
fn rigid_suffix_match<'a>(u: &[&'a RE], v: &[&'a RE], p: &BasePattern) -> bool {
    if u.len() >= p.len() {
        let p = char_sets_of_pattern(&v[p.start..p.end]);
        rigid_match_at(&p, u, u.len() - p.len())
    } else {
        false
    }
}

/// Check whether all rigid patterns in a sequence are matched
/// - `u` is a sequence/concatenation of REs
/// - 'v' and 'patterns' define a sequence of rigid patterns
/// - return true if all patterns defined by 'v' and 'patterns' are matched by
///    successive, disjoint sub-sequences of `u`
/// This version does a left-to-right search in `u'
#[allow(clippy::many_single_char_names)]
fn find_rigid_matches<'a>(u: &[&'a RE], v: &[&'a RE], patterns: &mut [BasePattern]) -> bool {
    let mut i = 0;
    for p in patterns {
        if p.is_rigid {
            let pattern = char_sets_of_pattern(&v[p.start..p.end]);
            match next_rigid_match(&pattern, u, i) {
                SearchResult::NotFound => return false,
                SearchResult::Found(j, k) => {
                    p.set_match(j, k);
                    i = k;
                }
            }
        }
    }
    true
}

/// Same a [find_rigid_matches] but with a right-to-left search
#[allow(clippy::many_single_char_names)]
fn find_rigid_matches_rev<'a>(u: &[&'a RE], v: &[&'a RE], patterns: &mut [BasePattern]) -> bool {
    let mut i = u.len();
    for p in patterns.iter_mut().rev() {
        if p.is_rigid {
            let pattern = char_sets_of_pattern(&v[p.start..p.end]);
            match prev_rigid_match(&pattern, u, i) {
                SearchResult::NotFound => return false,
                SearchResult::Found(j, k) => {
                    p.set_match(j, k);
                    i = j;
                }
            }
        }
    }
    true
}

// set the matching regions of every flexible pattern of b after rigid patterns
// have been matched. We use the fact that the predecessor and successor of a flexible
// pattern p are both rigid.
// So p.start_match = pred(p).end_match and p.end_match = suc(p).start_match.
fn set_flexible_regions(p: &mut [BasePattern], string_len: usize) {
    for i in 0..p.len() {
        if !p[i].is_rigid {
            let prev = if i == 0 { 0 } else { p[i - 1].end_match };
            let next = if i == p.len() - 1 {
                string_len
            } else {
                p[i + 1].start_match
            };
            p[i].set_match(prev, next);
        }
    }
}

// check whether u matches v
// TBD: improve this
fn flexible_match<'a>(_u: &[&'a RE], v: &[&'a RE]) -> bool {
    v.len() == 1 && v[0].expr.is_full()
}

// try to complete a partial matching, where all rigid base_patterns are matched
fn match_flexible_patterns<'a>(u: &[&'a RE], v: &[&'a RE], patterns: &mut [BasePattern]) -> bool {
    if patterns.is_empty() {
        // equivalent to matching with epsilon
        u.is_empty()
    } else {
        set_flexible_regions(patterns, u.len());
        for p in patterns {
            if !p.is_rigid && !flexible_match(&u[p.start_match..p.end_match], &v[p.start..p.end]) {
                return false;
            }
        }
        true
    }
}

// shift all base_patterns of p by delta (subtract delta)
fn shift_pattern_start(patterns: &mut [BasePattern], delta: usize) {
    for p in patterns {
        debug_assert!(p.end > p.start && p.start >= delta);
        p.start -= delta;
        p.end -= delta;
    }
}

// check whether (concat u) is a sub-language of (concat v)
// - u and v are non-empty
// - elements of u and v can be comp, inter, union, loop, range
fn concat_inclusion<'a>(u: &[&'a RE], v: &[&'a RE]) -> bool {
    let mut b = base_patterns(v);
    let mut p = b.as_mut_slice();
    let mut u = u;
    let mut v = v;

    // a rigid prefix must match
    if let Some(pat) = p.first() {
        if pat.is_rigid {
            if rigid_prefix_match(u, v, pat) {
                let len = pat.len();
                p = &mut p[1..];
                shift_pattern_start(p, len);
                u = &u[len..];
                v = &v[len..];
            } else {
                return false;
            }
        }
    }

    // a rigid suffix must match
    if let Some(pat) = p.last() {
        if pat.is_rigid {
            if rigid_suffix_match(u, v, pat) {
                let len = pat.len();
                let p_len = p.len();
                p = &mut p[..p_len - 1];
                u = &u[..u.len() - len];
                v = &v[..v.len() - len];
            } else {
                return false;
            }
        }
    }

    if find_rigid_matches(u, v, p) && match_flexible_patterns(u, v, p) {
        return true;
    }

    if find_rigid_matches_rev(u, v, p) && match_flexible_patterns(u, v, p) {
        return true;
    }

    false
}

///
/// Check language inclusion
///
/// This relies on simple/incomplete checks
/// - if the function returns true then `r` is a sub-language of `s`
/// - otherwise, we don't know.
///
fn sub_language<'a>(r: &'a RE, s: &'a RE) -> bool {
    use BaseRegLan::*;

    if r == s {
        true
    } else {
        match (&r.expr, &s.expr) {
            (Empty, _) => true,
            (_, Empty) => false,
            (Epsilon, _) => s.nullable,
            (_, Epsilon) => false,
            (Complement(r1), Complement(s2)) => sub_language(s2, r1),

            // for union and intersection, we iterate through the list only if the other side is simple
            // (i.e., it's either an atom or a concatenation/loop)
            (_, Union(list)) => {
                r.expr.concat_or_atomic() && list.iter().any(|&x| sub_language(r, x))
            }
            (Inter(list), _) => {
                s.expr.concat_or_atomic() && list.iter().any(|&x| sub_language(x, s))
            }
            (Union(list), _) => {
                s.expr.concat_or_atomic() && list.iter().all(|&x| sub_language(x, s))
            }
            (_, Inter(list)) => {
                r.expr.concat_or_atomic() && list.iter().all(|&x| sub_language(r, x))
            }

            // concatenation of loops and ranges
            (_, _) => {
                let u = decompose_concat(r);
                let v = decompose_concat(s);
                concat_inclusion(&u, &v)
            }
        }
    }
}

///
/// Simplify a vector for building unions or intersections of languages
/// - v = a vector of languages
/// - bottom = neutral element
/// - top = absorbing element
///
/// The function updates v to remove neutral elements and complementary pairs.
/// This implements the following simplification rules where op is either union
/// or intersection:
///  - op(X, bottom) = X
///  - op(top, X) = top
///  - op(X, complement(X)) = top
///  - op(X, X) = X
///
/// For op=intersection, we must have bottom = full and top = empty
///
/// For op=union, we must have bottom = empty and top = full
//
// We use the property that X and complement(X) have successive ids
// so after sorting v, X and complement(X) occur next to each other in v.
//
fn simplify_set_operation<'a>(v: &mut Vec<&'a RE>, bottom: &'a RE, top: &'a RE) {
    if !v.is_empty() {
        v.sort();
        v.dedup();
        if contains(v, top) {
            set_to_singleton(v, top)
        } else {
            let mut j = 0;
            let mut previous = v[0];
            if previous != bottom {
                v[j] = previous;
                j += 1;
            }
            for i in 1..v.len() {
                let current = v[i];
                if current.id == previous.id + 1 {
                    // current is the complement of previous
                    set_to_singleton(v, top);
                    return;
                }
                if current != bottom {
                    v[j] = current;
                    previous = current;
                    j += 1;
                }
            }
            v.truncate(j)
        }
    }
}

///
/// Pairs RegLan, ClassId used as keys in hash maps.
///
/// - Some(i) means the i-th interval of an RE's deriv_class
/// - None means the RE's complementary class
///
#[derive(Debug, PartialEq, Eq, Hash)]
struct DerivKey(RegLan, ClassId);

/// A store for constructing regular expressions using hash-consing.
///
/// The store ensures that each regular expression has a unique integer id.
///
/// For all regular expressions e1 and e2 constructed with the same manager,
/// we have e1.expr == e2.expr iff e1.id == e2.id
///
/// # Examples
///
/// This example shows how to create the regular expression `(ac + bc)*` and
/// compute its derivatives.
///
/// ```
/// use amzn_smt_strings::regular_expressions::*;
///
/// let re = &mut ReManager::new();
/// let ac = re.str(&"ac".into());  // ac
/// let bc = re.str(&"bc".into());  // bc
/// let sum = re.union(ac, bc);     // ac + bc
/// let e = re.star(sum);           // (ac + bc)*
///
/// let d1 = re.char_derivative(e, 'a' as u32); // derivative of e w.r.t. 'a'
/// let d2 = re.char_derivative(e, 'b' as u32); // derivative of e w.r.t. 'b'
///
/// // by hash-consing: d1 and d2 are equal
/// assert_eq!(d1, d2);
/// assert!(std::ptr::eq(d1, d2));
/// ```
//
// We maintain the invariant that x and complement(x) have successive
// ids.
#[derive(Debug)]
pub struct ReManager {
    store: Store<RE>,
    id2re: Vec<RegLan>, // map id to RE
    sigma: RegLan,      // all one-letter strings
    empty: RegLan,
    sigma_star: RegLan, // complement of empty (all strings)
    epsilon: RegLan,
    sigma_plus: RegLan, // complement of epsilon (all strings of positive length)
    deriv_cache: HashMap<DerivKey, RegLan>, // cache of known derivatives
}

impl ReManager {
    /// Create a new ReManager
    pub fn new() -> Self {
        let mut store = Store::new();
        let sigma = store.make(BaseRegLan::Range(CharSet::all_chars()));
        let not_sigma = store.make(BaseRegLan::Complement(sigma));
        let empty = store.make(BaseRegLan::Empty);
        let sigma_star = store.make(BaseRegLan::Loop(sigma, LoopRange::star()));
        let epsilon = store.make(BaseRegLan::Epsilon);
        let sigma_plus = store.make(BaseRegLan::Loop(sigma, LoopRange::plus()));
        debug_assert_eq!(sigma.id, 0);
        debug_assert_eq!(not_sigma.id, 1);
        debug_assert_eq!(empty.id, 2);
        debug_assert_eq!(sigma_star.id, 3);
        debug_assert_eq!(epsilon.id, 4);
        debug_assert_eq!(sigma_plus.id, 5);
        ReManager {
            store,
            id2re: vec![sigma, not_sigma, empty, sigma_star, epsilon, sigma_plus],
            sigma,
            empty,
            sigma_star,
            epsilon,
            sigma_plus,
            deriv_cache: HashMap::new(),
        }
    }

    fn id_to_re(&self, id: usize) -> RegLan {
        self.id2re[id]
    }

    /// Internal hash-consing constructor
    ///
    /// - When we create X, we also create complement(X) to make
    ///   sure X and complement(X) have consecutive ids.
    fn make(&mut self, ast: BaseRegLan) -> RegLan {
        match ast {
            BaseRegLan::Complement(x) => self.id_to_re(x.id + 1),
            _ => {
                let i = self.store.counter;
                debug_assert!(i == self.id2re.len());
                let x = self.store.make(ast);
                debug_assert!(x.id <= i);
                if x.id == i {
                    // new term
                    let y = self.store.make(BaseRegLan::Complement(x));
                    debug_assert!(y.id == i + 1);
                    self.id2re.push(x);
                    self.id2re.push(y);
                }
                x
            }
        }
    }

    /// The empty language
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new(); // create a manager
    /// let e = re.empty();        // get the empty language
    ///
    /// // no string belongs to e.
    /// assert!(! re.str_in_re(&"0129".into(), e));
    /// ```
    pub fn empty(&self) -> RegLan {
        self.empty
    }

    /// The full language
    ///
    /// This language contains every strings. It's the complement of [empty](Self::empty).
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new(); // create a manager
    /// let e = re.full();        // get the full language
    ///
    /// // every string belongs to e.
    /// assert!(re.str_in_re(&"0129".into(), e));
    /// ```
    pub fn full(&self) -> RegLan {
        self.sigma_star
    }

    /// The RE that contains only the empty string
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    /// let e = re.epsilon();
    ///
    /// // the empty string belongs to e
    /// assert!(re.str_in_re(&"".into(), e));
    /// // a non-empty string does not belong to e
    /// assert!(! re.str_in_re(&"a".into(), e));
    /// ```
    pub fn epsilon(&self) -> RegLan {
        self.epsilon
    }

    /// The RE that contains all non-empty strings
    ///
    /// This is the complement of [epsilon](Self::epsilon).
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    /// let e = re.sigma_plus();
    ///
    /// // the empty string does not belong to e
    /// assert!(! re.str_in_re(&"".into(), e));
    /// // any non-empty string belongs to e
    /// assert!(re.str_in_re(&"a".into(), e));
    /// ```
    pub fn sigma_plus(&self) -> RegLan {
        self.sigma_plus
    }

    /// Regular expression defined by a character set
    ///
    /// Return the regular expression that contains all single-character
    /// strings with characters in the specified set. See also [range](Self::range).
    ///
    /// # Example
    ///
    /// Lower-case letters in ASCII.
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    /// use amzn_smt_strings::character_sets::*;
    ///
    /// let mut re = ReManager::new();
    /// let set = CharSet::range('a' as u32, 'z' as u32);
    /// let e = re.char_set(set);
    ///
    /// // a single-character string that's in e
    /// assert!(re.str_in_re(&"c".into(), e));
    /// // a single-character string that's not in e
    /// assert!(!re.str_in_re(&"7".into(), e));
    /// // strings with more than one characters are not in e
    /// assert!(!re.str_in_re(&"abc".into(), e));
    /// ```
    pub fn char_set(&mut self, set: CharSet) -> RegLan {
        self.make(BaseRegLan::Range(set))
    }

    ///
    /// Complement of a language
    ///
    /// Return the complement of RE `e`.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    /// let a_single_digit = re.range('0' as u32, '9' as u32);
    /// let not_a_digit = re.complement(a_single_digit);
    ///
    /// assert!(re.str_in_re(&"7".into(), a_single_digit));
    /// assert!(! re.str_in_re(&"7".into(), not_a_digit));
    ///
    /// // any string of more than 2 characters is not a single digit!
    /// assert!(re.str_in_re(&"94".into(), not_a_digit))
    /// ```
    pub fn complement(&mut self, e: RegLan) -> RegLan {
        self.id_to_re(e.id ^ 1)
    }

    /// Concatenation of two languages
    ///
    /// Concatenate languages `e1` and `e2` in that order.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    /// let a_letter = re.range('a' as u32, 'z' as u32);
    /// let a_digit = re.range('0' as u32, '9' as u32);
    /// let e = re.concat(a_letter, a_digit);
    ///
    /// assert!(re.str_in_re(&"h4".into(), e));
    /// ```
    pub fn concat(&mut self, e1: RegLan, e2: RegLan) -> RegLan {
        match (&e1.expr, &e2.expr) {
            // empty . R --> empty
            (BaseRegLan::Empty, _) => self.empty,
            (_, BaseRegLan::Empty) => self.empty,
            // epsilon . R --> R
            (BaseRegLan::Epsilon, _) => e2,
            (_, BaseRegLan::Epsilon) => e1,
            // R . R^[i,j] --> R^[i+1, j+1]
            (_, BaseRegLan::Loop(&ref y, rng)) if *e1 == *y => {
                self.make(BaseRegLan::Loop(e1, rng.add_point(1)))
            }
            (BaseRegLan::Loop(&ref x, rng), _) if *e2 == *x => {
                self.make(BaseRegLan::Loop(e2, rng.add_point(1)))
            }
            // R^[a,b] . R^[b,c] -> R^[a+b, b+c]
            (BaseRegLan::Loop(&ref x, x_rng), BaseRegLan::Loop(&ref y, y_rng)) if *x == *y => {
                self.make(BaseRegLan::Loop(x, x_rng.add(y_rng)))
            }
            // R . R -> R^2
            _ if *e1 == *e2 => self.make(BaseRegLan::Loop(e1, LoopRange::point(2))),
            // (R . S) . T -> R . (S . T)
            (BaseRegLan::Concat(x, y), _) => {
                let right = self.concat(y, e2);
                self.concat(x, right)
            }
            //
            _ => {
                if e1.nullable && e2 == self.sigma_star {
                    // S . Sigma^* --> Sigma^* if S is nullable
                    e2
                } else {
                    self.make(BaseRegLan::Concat(e1, e2))
                }
            }
        }
    }

    /// Concatenation of multiple languages
    ///
    /// Build the concatenation of `a[0]`, `a[1]`, ... in this order.
    /// - return [epsilon](Self::epsilon) is `a` is empty.
    /// - return `a[0]` is `a.len() == 1`
    ///
    /// See [concat](Self::concat)
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let a_letter = re.range('a' as u32, 'z' as u32);
    /// let a_digit = re.range('0' as u32, '9' as u32);
    /// let e = re.concat_list([a_letter, a_letter, a_digit]);
    ///
    /// assert!(re.str_in_re(&"ab3".into(), e));
    /// ```
    pub fn concat_list(&mut self, a: impl IntoIterator<Item = RegLan>) -> RegLan {
        let mut v = Vec::new();
        for x in a {
            flatten_concat(x, &mut v);
        }
        let mut result = self.epsilon;
        for &x in v.iter().rev() {
            result = self.concat(x, result);
        }
        result
    }

    /// Generalized loop
    ///
    /// Parameter `range` defines an interval of natural numbers `[i, j]` where `j` may be infinity.
    /// This method returns the regular language equal to the union of `e`<sup>k</sup> for k in the interval `[i, j]`.
    /// See [loop_ranges](crate::loop_ranges).
    ///
    /// # Example
    ///
    /// Regular expression that recognizes sequences of 3 to 5 digits.
    ///
    /// ```
    /// use amzn_smt_strings::{regular_expressions::*, loop_ranges::*};
    ///
    /// let mut re = ReManager::new();
    ///
    /// let digits = re.range('0' as u32, '9' as u32);
    /// let e = re.mk_loop(digits, LoopRange::finite(3, 5));
    ///
    /// assert!(re.str_in_re(&"12345".into(), e));
    /// assert!(! re.str_in_re(&"123456".into(), e));
    /// ```
    pub fn mk_loop(&mut self, e: RegLan, range: LoopRange) -> RegLan {
        if range.is_zero() {
            // R ^ 0 --> epsilon
            self.epsilon
        } else if range.is_one() {
            // R ^ 1 --> R
            e
        } else {
            match &e.expr {
                // empty ^ [i, j] --> empty
                BaseRegLan::Empty => self.empty,
                // epsilon ^ [i, j] --> epsilon
                BaseRegLan::Epsilon => self.epsilon,
                // (R ^[i,j]) ^ [k, l] --> R ^[i *k, j*l] if the product is exact
                BaseRegLan::Loop(&ref x, x_rng) if x_rng.right_mul_is_exact(&range) => {
                    self.make(BaseRegLan::Loop(x, x_rng.mul(&range)))
                }
                _ => self.make(BaseRegLan::Loop(e, range)),
            }
        }
    }

    // Intersection of REs in v
    fn make_inter(&mut self, mut v: Vec<RegLan>) -> RegLan {
        simplify_set_operation(&mut v, self.sigma_star, self.empty);
        if contains(&v, self.epsilon) {
            // v contains epsilon: the intersection is either epsilon or empty
            if v.iter().all(|&r| r.nullable) {
                self.epsilon
            } else {
                self.empty
            }
        } else {
            match v.len() {
                0 => self.sigma_star,
                1 => v[0],
                _ => self.make(BaseRegLan::Inter(v.into())),
            }
        }
    }

    // Union of REs in v
    fn make_union(&mut self, mut v: Vec<RegLan>) -> RegLan {
        // verbose version of 'sub_language'
        #[allow(dead_code)]
        fn is_included(r: RegLan, s: RegLan) -> bool {
            let result = sub_language(r, s);
            if result {
                println!("---> subsumption: {} subsumed by {}", r, s);
            }
            result
        }

        // we skip the subsumption check when x == r
        // this works since there are no duplicates in a
        fn is_subsumed(r: RegLan, a: &[RegLan]) -> bool {
            // a.iter().any(|&x| x != r && is_included(r, x))
            a.iter().any(|&x| x != r && sub_language(r, x))
        }

        fn remove_subsumed(a: &mut Vec<RegLan>) {
            let mut i = 0;
            while i < a.len() {
                if is_subsumed(a[i], a) {
                    a.remove(i);
                } else {
                    i += 1;
                }
            }
        }

        simplify_set_operation(&mut v, self.empty, self.sigma_star);
        if v.len() >= 2 {
            remove_subsumed(&mut v);
        }
        match v.len() {
            0 => self.empty,
            1 => v[0],
            _ => self.make(BaseRegLan::Union(v.into())),
        }
    }

    /// Intersection of two languages
    ///
    /// Return the intersection of `e1` and `e2`
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let sigma = re.all_chars();
    /// let b = re.exp(sigma, 4);    // all strings of length 4
    ///
    /// let digits = re.range('0' as u32, '9' as u32);
    /// let c = re.star(digits);    // all sequences of digits
    ///
    /// let e = re.inter(b, c);     // all sequences of four digits
    ///
    /// assert!(re.str_in_re(&"0000".into(), e));
    /// ```
    pub fn inter(&mut self, e1: RegLan, e2: RegLan) -> RegLan {
        let mut v = Vec::new();
        flatten_inter(e1, &mut v);
        flatten_inter(e2, &mut v);
        self.make_inter(v)
    }

    /// Intersection of multiple languages
    ///
    /// This returns the intersection of `a[0]`, `a[1]`, etc.
    /// - return the full language (see [full](Self::full)) if `a` is empty
    /// - return `a[0]` if `a.len() == 1`
    /// - otherwise construct the intersection.
    ///
    /// See [inter](Self::inter) for an example.
    pub fn inter_list(&mut self, a: impl IntoIterator<Item = RegLan>) -> RegLan {
        let mut v = Vec::new();
        for r in a {
            flatten_inter(r, &mut v);
        }
        self.make_inter(v)
    }

    /// Union of two languages
    ///
    /// Return the union of `e1` and `e2`.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let abc = re.str(&"abc".into());
    /// let de = re.str(&"de".into());
    /// let u = re.union(abc, de);
    ///
    /// // u contains two strings: "abc" and "de"
    /// assert!(re.str_in_re(&"de".into(), u));
    /// assert!(re.str_in_re(&"abc".into(), u));
    /// ```
    pub fn union(&mut self, e1: RegLan, e2: RegLan) -> RegLan {
        let mut v = Vec::new();
        flatten_union(e1, &mut v);
        flatten_union(e2, &mut v);
        self.make_union(v)
    }

    /// Union of several languages
    ///
    /// Return the union of `a[0]`, `a[1]`, ...
    /// - if `a` is empty, return the empty language (see [empty](Self::empty))
    /// - if `a.len() == 1`, return `a[0]`
    /// - otherwise, build the union.
    ///
    /// See [union](Self::union).
    ///
    pub fn union_list(&mut self, a: impl IntoIterator<Item = RegLan>) -> RegLan {
        let mut v = Vec::new();
        for r in a {
            flatten_union(r, &mut v);
        }
        self.make_union(v)
    }

    /// Difference of two languages
    ///
    /// Return the difference of `e1` and `e2`. This is the same as
    /// the intersection of `e1` and the complement of `e2`.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let sigma = re.all_chars();
    /// let b = re.exp(sigma, 4);    // all strings of length 4
    ///
    /// let digits = re.range('0' as u32, '9' as u32);
    /// let c = re.star(digits);    // all sequences of digits
    ///
    /// let e = re.diff(c, b);  // sequences of digits of length other than four
    ///
    /// assert!(re.str_in_re(&"".into(), e)); // the empty sequence is included
    /// assert!(! re.str_in_re(&"0000".into(), e));
    /// assert!(re.str_in_re(&"123456".into(), e));
    /// ```
    pub fn diff(&mut self, e1: RegLan, e2: RegLan) -> RegLan {
        let comp_e2 = self.complement(e2);
        self.inter(e1, comp_e2)
    }

    /// Difference of several languages
    ///
    /// Return the difference of `e1` and all regular expressions of `a`
    /// - return `e1` if `a` is empty.
    ///
    pub fn diff_list(&mut self, e1: RegLan, a: impl IntoIterator<Item = RegLan>) -> RegLan {
        let mut v = Vec::new();
        flatten_inter(e1, &mut v);
        for r in a {
            flatten_inter(self.complement(r), &mut v);
        }
        self.make_inter(v)
    }

    /// All one-character strings
    ///
    /// This is the same as `range(CharSet::all_chars)`. See [range](Self::range) and [CharSet::all_chars].
    ///
    /// See [diff](Self::diff) for an example.
    pub fn all_chars(&mut self) -> RegLan {
        self.sigma
    }

    /// A character as a regular expression
    ///
    /// Return the language that contains the one-character string `x` and nothing else.
    /// - this is the same as `char_set(CharSet::singleton(x))`. See [char_set](Self::char_set)
    ///   and [CharSet::singleton].
    ///
    /// # Panics
    ///
    /// If x is not a valid SMT character (i.e., x > MAX_CHAR).
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let e = re.char('Z' as u32);
    ///
    /// assert!(re.str_in_re(&"Z".into(), e));
    /// ```
    pub fn char(&mut self, x: u32) -> RegLan {
        assert!(x <= MAX_CHAR);
        self.char_set(CharSet::singleton(x))
    }

    /// Range of characters
    ///
    /// Return the language that contains all one-character strings that contains character in range [start, end]
    /// - this is the same as `char_set(CharSet::range(start, end))`. See [char_set](Self::char_set)
    ///   and [CharSet::range].
    ///
    /// # Panics
    ///
    /// If the range is empty (i.e., start > end) or if end > [MAX_CHAR].
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let e = re.range('0' as u32, '9' as u32);
    ///
    /// assert!(re.str_in_re(&"4".into(), e));
    /// ```
    pub fn range(&mut self, start: u32, end: u32) -> RegLan {
        assert!(start <= end && end <= MAX_CHAR);
        self.char_set(CharSet::range(start, end))
    }

    /// Kleene star closure
    ///
    /// Return the star closure of language `e` (i.e., the concatenations of an arbitrary number
    /// of strings of `e`).
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let letters = re.range('a' as u32, 'z' as u32);
    /// let letter_sequences = re.star(letters);
    ///
    /// assert!(re.str_in_re(&"abcd".into(), letter_sequences));
    /// assert!(re.str_in_re(&"".into(), letter_sequences));
    /// assert!(! re.str_in_re(&"abc-def".into(), letter_sequences));
    /// ```
    pub fn star(&mut self, e: RegLan) -> RegLan {
        self.mk_loop(e, LoopRange::star())
    }

    /// Kleene plus
    ///
    /// Return the closure of `e` (i.e., the concatenation of one or more strings of `e`)
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let letters = re.range('a' as u32, 'z' as u32);
    /// let letter_sequences = re.plus(letters);
    ///
    /// assert!(re.str_in_re(&"abcd".into(), letter_sequences));
    /// assert!(! re.str_in_re(&"".into(), letter_sequences));
    /// assert!(! re.str_in_re(&"abc-def".into(), letter_sequences));
    /// ```
    pub fn plus(&mut self, e: RegLan) -> RegLan {
        self.mk_loop(e, LoopRange::plus())
    }

    /// Option
    ///
    /// Returns the union of [epsilon](Self::epsilon) and `e`.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let e = re.char('A' as u32);
    /// let opt_e = re.opt(e);
    ///
    /// // Both "A" and the empty strings are in `opt_e`
    /// assert!(re.str_in_re(&"A".into(), opt_e));
    /// assert!(re.str_in_re(&"".into(), opt_e));
    /// ```
    pub fn opt(&mut self, e: RegLan) -> RegLan {
        self.mk_loop(e, LoopRange::opt())
    }

    /// Exponentiation
    ///
    /// Concatenates `e` with itself `k` times.
    /// - return [epsilon](Self::epsilon) if `k==0`.
    ///
    /// # Example
    ///
    /// All strings of length 5.
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let a = re.all_chars();
    /// let b = re.exp(a, 5);
    ///
    /// assert!(re.str_in_re(&"ABCDE".into(), b));
    /// assert!(! re.str_in_re(&"ABCD".into(), b));
    /// ```
    pub fn exp(&mut self, e: RegLan, k: u32) -> RegLan {
        self.mk_loop(e, LoopRange::point(k))
    }

    /// Finite loop as defined in SMT-LIB
    ///
    /// - if `i <= j`, return the regular expression `Loop(e, [i, j])`.
    ///   See [mk_loop](Self::mk_loop)
    /// - if `i > j`, return the empty language. See [empty](Self::empty).
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let a = re.all_chars();
    /// let b = re.smt_loop(a, 3, 7); // strings of length 3 to 7
    ///
    /// assert!(re.str_in_re(&"abcdef".into(), b));
    /// ```
    pub fn smt_loop(&mut self, e: RegLan, i: u32, j: u32) -> RegLan {
        if i <= j {
            self.mk_loop(e, LoopRange::finite(i, j))
        } else {
            self.empty
        }
    }

    /// Character range as defined in SMT-LIB
    ///
    /// - if `s1` and `s2` are both singleton strings, and `s1 <= s2` in the
    ///   lexicographic ordering, return self.range(CharSet::range(c1, c2)) where c1 = unique
    ///   character of s1 and c2 = unique character of s2.
    /// - otherwise, return the empty language
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let b = re.smt_range(&"a".into(), &"z".into());
    ///
    /// assert!(re.str_in_re(&"h".into(), b));
    /// ```
    pub fn smt_range(&mut self, s1: &SmtString, s2: &SmtString) -> RegLan {
        if s1.len() == 1 && s2.len() == 1 {
            let c1 = s1.char(0);
            let c2 = s2.char(0);
            if c1 <= c2 {
                return self.char_set(CharSet::range(c1, c2));
            }
        }
        self.empty
    }

    /// Language that contains a single string
    ///
    /// - Return the language that contains string `s` and nothing else.
    /// - This is the same as the SMT-LIB 'str.to_re' function.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let s = re.str(&"alpha".into());
    ///
    /// assert!(re.str_in_re(&"alpha".into(), s));
    /// assert!(! re.str_in_re(&"beta".into(), s));
    /// ```
    pub fn str(&mut self, s: &SmtString) -> RegLan {
        let mut re = self.epsilon();
        for c in s.iter().rev() {
            let c = self.char(*c);
            re = self.concat(c, re);
        }
        re
    }

    //
    // DERIVATIVES
    //

    /// Compute the derivative w.r.t. c of all elements of list
    fn deriv_list(&mut self, list: &[RegLan], c: u32) -> Vec<RegLan> {
        list.iter().map(|r| self.deriv(r, c)).collect()
    }

    /// Derivative of e with respect to a character c
    fn compute_derivative(&mut self, e: RegLan, c: u32) -> RegLan {
        match e.expr {
            BaseRegLan::Empty => self.empty,
            BaseRegLan::Epsilon => self.empty,
            BaseRegLan::Range(r) => {
                if r.contains(c) {
                    self.epsilon
                } else {
                    self.empty
                }
            }
            BaseRegLan::Concat(e1, e2) => {
                let d1 = self.deriv(e1, c);
                let d1 = self.concat(d1, e2);
                if e1.nullable {
                    let d2 = self.deriv(e2, c);
                    self.union(d1, d2)
                } else {
                    d1
                }
            }
            BaseRegLan::Loop(e1, range) => {
                let d1 = self.deriv(e1, c);
                let e2 = self.mk_loop(e1, range.shift());
                self.concat(d1, e2)
            }
            BaseRegLan::Complement(e1) => {
                let d1 = self.deriv(e1, c);
                self.complement(d1)
            }
            BaseRegLan::Inter(ref v) => {
                let d = self.deriv_list(&v[..], c);
                self.inter_list(d)
            }
            BaseRegLan::Union(ref v) => {
                let d = self.deriv_list(&v[..], c);
                self.union_list(d)
            }
        }
    }

    /// Derivative with respect to a character c using the cache
    fn deriv(&mut self, e: RegLan, c: u32) -> RegLan {
        let cid = e.class_of_char(c);
        self.cached_deriv(e, cid)
    }

    ///
    /// Check whether character c can start expression e
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let mut re = ReManager::new();
    ///
    /// let digits = re.range('0' as u32, '9' as u32);
    /// let s = re.star(digits);
    ///
    /// assert!(re.start_char(s, '1' as u32));
    /// assert!(! re.start_char(s, 'a' as u32));
    /// ```
    pub fn start_char(&mut self, e: RegLan, c: u32) -> bool {
        match &e.expr {
            BaseRegLan::Empty => false,
            BaseRegLan::Epsilon => false,
            BaseRegLan::Range(set) => set.contains(c),
            BaseRegLan::Concat(e1, e2) => {
                self.start_char(e1, c) || e1.nullable && self.start_char(e2, c)
            }
            BaseRegLan::Loop(e, _) => self.start_char(e, c),
            BaseRegLan::Inter(args) => args.iter().all(|x| self.start_char(x, c)),
            BaseRegLan::Union(args) => args.iter().any(|x| self.start_char(x, c)),
            BaseRegLan::Complement(_) => {
                // expensive case
                let d = self.deriv(e, c);
                !self.is_empty_re(d)
            }
        }
    }

    ///
    /// Check whether all characters in class cid can start e
    /// - return Error if cid is not a valid class for e
    ///
    pub fn start_class(&mut self, e: RegLan, cid: ClassId) -> Result<bool, Error> {
        if e.valid_class_id(cid) {
            let c = e.pick_class_rep(cid);
            Ok(self.start_char(e, c))
        } else {
            Err(Error::BadClassId)
        }
    }

    ///
    /// Cached derivative
    ///
    /// - cid identifies a derivative class of e.
    /// - cid must be either Interval(i) where i is the id of a deriv class of e
    ///   or Complement, which denotes the complementary class of e.
    ///
    /// In either cases, all characters in the class are equivalent:
    /// - if c1 and c2 are in deriv class i then deriv(e, c1) = deriv(e, c2)
    /// - if c1 and c2 are outside all deriv class then deriv(e, c1) = deriv(e, c2)
    ///
    /// This method panics in the following cases:
    /// - cid is Interval(i) but i is not the index of a derivative class of e
    /// - cid is Complementary but the complementary derivative class of e is empty.
    ///
    fn cached_deriv(&mut self, e: RegLan, cid: ClassId) -> RegLan {
        let key = DerivKey(e, cid);
        match self.deriv_cache.get(&key) {
            Some(&r) => r,
            None => {
                let c = e.pick_class_rep(cid);
                let r = self.compute_derivative(e, c);
                self.deriv_cache.insert(key, r);
                r
            }
        }
    }

    ///
    /// Derivative with respect to a class id
    ///
    /// Compute the derivative of e with respect to a class defined by `cid`
    /// - if `cid` is `Interval(i)`: class = i-th derivative class of `e`
    /// - if `cid` is `Complement`: class = complementary derivative class of `e`
    ///
    /// Derivative classes of `e` are indexed from 0 to `n`-1 where `n` is the
    /// number of classes.
    ///
    /// # Errors
    ///
    /// Return Err([Error::BadClassId]) if the class id is invalid.
    /// - Class id `Interval(i)` is invalid if i is larger than or equal to the number
    ///   of derivative classes of `e`.
    /// - Class if `Complement` is invalid if the complementary class of e is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::{regular_expressions::*, character_sets::*};
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let mut re = ReManager::new();
    ///
    /// let abc = re.str(&"abc".into());
    /// let efg = re.str(&"efg".into());
    /// let r = re.union(abc, efg); // 'abc' + 'efg': two derivative classes
    ///
    /// let n = r.num_deriv_classes();
    /// assert_eq!(n, 2);
    ///
    /// let test1 = re.class_derivative(r, ClassId::Interval(0))?;
    /// let test2 = re.class_derivative(r, ClassId::Interval(1))?;
    /// let test3 = re.class_derivative(r, ClassId::Complement)?;
    ///
    /// assert_eq!(test1, re.str(&"bc".into()));
    /// assert_eq!(test2, re.str(&"fg".into()));
    /// assert_eq!(test3, re.empty());
    /// # Ok(())
    /// # }
    /// ```
    pub fn class_derivative(&mut self, e: RegLan, cid: ClassId) -> Result<RegLan, Error> {
        if e.valid_class_id(cid) {
            Ok(self.cached_deriv(e, cid))
        } else {
            Err(Error::BadClassId)
        }
    }

    ///
    /// Unchecked derivative with respect to a class id
    ///
    /// Compute the derivative of e with respect to a class defined by cid.
    /// Does not check whether cid is a valid class id for e.
    /// See [class_derivative](Self::class_derivative)
    ///
    /// # Panics
    ///
    /// If cid is not a valid class id for e.
    ///
    pub fn class_derivative_unchecked(&mut self, e: RegLan, cid: ClassId) -> RegLan {
        self.cached_deriv(e, cid)
    }

    ///
    /// Derivative with respect to a character set
    ///
    /// Return the derivative of e with respect to c provided this is well defined.
    ///
    /// # Errors
    ///
    /// The derivative with respect to c is well defined either if c is included in a
    /// derivative class of e or if c is included in the complementary class.
    /// If these conditions do not hold, the method return Err([Error::UndefinedDerivative]).
    /// See [Error][crate::errors::Error].
    ///
    /// # Example
    /// ```
    /// use amzn_smt_strings::{regular_expressions::*, character_sets::*};
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let mut re = ReManager::new();
    ///
    /// let a_to_z = re.range('a' as u32, 'z' as u32);
    /// let e = re.plus(a_to_z); // non-empty sequences of lower-case ascii letters
    ///
    /// // the derivative of e w.r.t. ['c', 't'] is defined.
    /// let test = re.set_derivative(e, &CharSet::range('c' as u32, 't' as u32))?;
    ///
    /// assert_eq!(test, re.star(a_to_z));
    /// # Ok(())
    /// # }
    /// ```
    ///
    pub fn set_derivative(&mut self, e: RegLan, c: &CharSet) -> Result<RegLan, Error> {
        let cid = e.class_of_set(c)?;
        Ok(self.cached_deriv(e, cid))
    }

    ///
    /// Unchecked derivative with respect to a character set.
    ///
    /// See [derivative](Self::set_derivative).
    ///
    /// # Panics
    ///
    /// If the derivative is not defined for this character set.
    ///
    pub fn set_derivative_unchecked(&mut self, e: RegLan, c: &CharSet) -> RegLan {
        let cid = e.class_of_set(c).unwrap();
        self.cached_deriv(e, cid)
    }

    ///
    /// Derivative with respect to a character
    ///
    /// The derivative of e with respect to c is a regular expression e1 such
    /// every string of e that starts with c is formed by concatenating c and
    /// a string of e1. So the language of e1 is
    ///  L(e1) = { w | c.w is in L(e) }
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// fn sum_of_str(re: &mut ReManager, s1: &str, s2: &str) -> RegLan {
    ///     let s1 = re.str(&s1.into());
    ///     let s2 = re.str(&s2.into());
    ///     re.union(s1, s2)
    /// }
    ///
    /// let re = &mut ReManager::new();
    /// let e = sum_of_str(re, "abc", "acc");
    ///
    /// // e is 'abc + acc'
    /// // the derivative of e w.r.t. 'a' is 'bc + cc'
    /// let d = re.char_derivative(e, 'a' as u32);
    /// assert_eq!(d, sum_of_str(re, "bc", "cc"));
    /// ```
    pub fn char_derivative(&mut self, e: RegLan, c: u32) -> RegLan {
        debug_assert!(c <= MAX_CHAR);
        self.deriv(e, c)
    }

    ///
    /// Derivative with respect to a string
    ///
    /// The derivative with respect to s is defined by induction on the length of s:
    /// - if s is empty, deriv(e, s) = e
    /// - if s is of the form a.w, then deriv(e, s) = deriv(w, deriv(a, s))
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let re = &mut ReManager::new();
    /// let abc = re.str(&"abc".into());
    /// let acc = re.str(&"acc".into());
    /// let e = re.union(abc, acc);
    ///
    /// // e is 'abc + acc'
    /// // the derivative of e with respect to "ab" is 'c'
    /// let d1 = re.str_derivative(e, &"ab".into());
    /// assert_eq!(d1, re.char('c' as u32));
    ///
    /// // the derivative of e with respect to the empty string is e
    /// let d2 = re.str_derivative(e, &"".into());
    /// assert_eq!(d2, e);
    /// ```
    pub fn str_derivative(&mut self, e: RegLan, s: &SmtString) -> RegLan {
        s.iter().fold(e, |r, &c| self.char_derivative(r, c))
    }

    /// Construct an iterator to list the derivatives of a regular expression
    ///
    /// The iterator produces `e`, then the derivatives of `e`, then the derivatives
    /// of these derivatives, and so forth. There are finitely many such derivatives.
    /// The iterator produces them without duplicates.
    pub fn iter_derivatives(&mut self, e: RegLan) -> DerivativeIterator<'_> {
        let mut queue = BfsQueue::new();
        queue.push(e);
        DerivativeIterator {
            manager: self,
            queue,
        }
    }

    ///
    /// Check whether a string belongs to the language defined by a regular expression
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let re = &mut ReManager::new();
    ///
    /// // Build regular expression (ac + bc)*
    /// let ac = re.str(&"ac".into());
    /// let bc = re.str(&"bc".into());
    /// let sum = re.union(ac, bc);
    /// let e = re.star(sum);
    ///
    /// // Check that "acacbc" is in the language
    /// assert!(re.str_in_re(&"acacbc".into(), e))
    /// ```
    ///
    pub fn str_in_re(&mut self, s: &SmtString, e: RegLan) -> bool {
        self.str_derivative(e, s).nullable
    }

    ///
    /// Check whether a regular expression is empty
    ///
    /// # Example
    /// ```
    /// use amzn_smt_strings::regular_expressions::*;
    ///
    /// let re = &mut ReManager::new();
    ///
    /// let full = re.full();
    /// let abcd = re.str(&"abcd".into());
    /// let bc = re.str(&"bc".into());
    ///
    /// let a = re.concat(abcd, full); // strings that start with 'abcd'
    /// let b = re.concat_list([full, bc, full]); // strings that contain 'bc'
    ///
    /// let test = re.diff(a, b); // strings that start with 'abcd' but don't contain 'bc'
    /// assert!(re.is_empty_re(test));
    /// ```
    pub fn is_empty_re(&mut self, e: RegLan) -> bool {
        self.iter_derivatives(e).all(|x| !x.nullable)
    }

    ///
    /// Search for a symbolic string of e
    /// - the result is None, if e is an empty regular expression.
    /// - otherwise the result is Some(list or pairs (RegLan, ClassId) such that:
    ///   1) in each pair, the classId is valid for the RegLan
    ///   2) the RegLan in the first pair is e
    ///   3) in two successive pairs (r1, cid1) (r2, cid2),
    ///      we have r2 = class_derivative(r1, cid1)
    ///   4) for the last pair in the list (r, cid), the derivative
    ///      of r w.r.t. cid is nullable.
    /// - the list is empty if e itself is nullable (this represents the empty string)
    ///
    fn get_string_path(&mut self, e: RegLan) -> Option<Vec<(RegLan, ClassId)>> {
        let mut queue: LabeledQueue<RegLan, ClassId> = LabeledQueue::new(e);
        while let Some(r) = queue.pop() {
            if r.nullable {
                return queue.full_path(&r);
            } else {
                for cid in r.class_ids() {
                    let d = self.class_derivative_unchecked(r, cid);
                    queue.push(r, cid, d);
                }
            }
        }
        None
    }

    ///
    /// Get a string that belongs to a regular expression
    ///
    /// Return None if the regular expression `e` is empty.
    ///
    /// # Example
    /// ```
    /// use amzn_smt_strings::{regular_expressions::*, smt_strings::*};
    ///
    /// let re = &mut ReManager::new();
    ///
    /// let str1 = SmtString::from("abc");
    /// let str2 = SmtString::from("bcd");
    ///
    /// let abc = re.str(&str1);
    /// let bcd = re.str(&str2);
    /// let u = re.union(abc, bcd);
    ///
    /// let str = re.get_string(u);
    ///
    /// assert!(str == Some(str1) || str == Some(str2));
    /// ```
    pub fn get_string(&mut self, e: RegLan) -> Option<SmtString> {
        match self.get_string_path(e) {
            None => None,
            Some(path) => {
                let result: Vec<u32> = path
                    .iter()
                    .map(|(re, cid)| re.pick_class_rep(*cid))
                    .collect();
                Some(result.into())
            }
        }
    }

    //
    // try to compile to a DFA of no more than max_states.
    // return None if that fails (i.e., if the automaton will have more than max_states)
    //
    fn compile_with_bound(&mut self, e: RegLan, max_states: usize) -> Option<Automaton> {
        if max_states == 0 {
            None
        } else {
            let mut builder = AutomatonBuilder::new(&e.expr);
            let mut queue = BfsQueue::new();
            let mut state_count = 0;
            queue.push(e);
            while let Some(e) = queue.pop() {
                debug_assert!(state_count <= max_states);
                if state_count == max_states {
                    return None;
                }
                state_count += 1;
                for set in e.char_ranges() {
                    let d = self.set_derivative_unchecked(e, set);
                    queue.push(d);
                    builder.add_transition(&e.expr, set, &d.expr);
                }
                if !e.empty_complement() {
                    let d = self.class_derivative_unchecked(e, ClassId::Complement);
                    queue.push(d);
                    builder.set_default_successor(&e.expr, &d.expr);
                }
                if e.nullable {
                    builder.mark_final(&e.expr);
                }
            }
            Some(builder.build_unchecked())
        }
    }

    ///
    /// Compile a regular expression to a deterministic finite state automaton
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::{regular_expressions::*, automata::*};
    ///
    /// let re = &mut ReManager::new();
    ///
    /// // (ac + bc)*
    /// let ac = re.str(&"ac".into());
    /// let bc = re.str(&"bc".into());
    /// let sum = re.union(ac, bc);
    /// let e = re.star(sum);
    ///
    /// // convert e to an automaton
    /// let auto = re.compile(e);
    ///
    /// // string accepted by the automaton
    /// assert!(auto.accepts(&"acbcbc".into()))
    /// ```
    pub fn compile(&mut self, e: RegLan) -> Automaton {
        self.compile_with_bound(e, usize::MAX).unwrap()
    }

    ///
    /// Compile a regular expression to a DFA of bounded size
    ///
    /// Try to compile a regular expression `e` to a deterministic finite-state automaton
    /// of size no more than `max_states`.
    /// - e: regular expression
    /// - max_states: bound
    ///
    /// Return None if the DFA has more than `max_states`
    /// Return `Some(a)` otherwise where `a` is the automaton
    ///
    /// # Example
    ///
    /// ```
    /// use amzn_smt_strings::{regular_expressions::*, automata::*};
    ///
    /// let re = &mut ReManager::new();
    ///
    /// // (ac + bc)+
    /// let ac = re.str(&"ac".into());
    /// let bc = re.str(&"bc".into());
    /// let sum = re.union(ac, bc);
    /// let e = re.plus(sum);
    ///
    /// // the smallest DFA that recognizes e has four states
    /// let test1 = re.try_compile(e, 3);
    /// assert!(test1.is_none());
    ///
    /// let test2 = re.try_compile(e, 4);
    /// assert!(test2.is_some());
    /// ```
    pub fn try_compile(&mut self, e: RegLan, max_states: usize) -> Option<Automaton> {
        self.compile_with_bound(e, max_states)
    }
}

impl Default for ReManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator to enumerate all the derivatives of a regular expression
///
/// See [iter_derivatives](crate::regular_expressions::ReManager::iter_derivatives).
#[derive(Debug)]
pub struct DerivativeIterator<'a> {
    queue: BfsQueue<RegLan>,
    manager: &'a mut ReManager,
}

impl<'a> Iterator for DerivativeIterator<'a> {
    type Item = &'a RE;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(r) = self.queue.pop() {
            for cid in r.class_ids() {
                let d = self.manager.class_derivative_unchecked(r, cid);
                self.queue.push(d);
            }
            Some(r)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::smt_strings::char_to_smt;

    use super::*;

    fn print_term(name: &str, r: RegLan) {
        println!("term {} = {}", name, r);
        println!("   ptr:       {:p}", r);
        println!("   id:        {}", r.id);
        println!("   nullable:  {}", r.nullable);
        println!("   singleton: {}", r.singleton);
        println!("   pattern:   {}", r.simple_pattern);
        println!("   deriv:     {}", r.deriv_class);
        println!();
    }

    fn build_atoms(re: &mut ReManager) -> Vec<RegLan> {
        vec![
            re.empty(),
            re.epsilon(),
            re.all_chars(),
            re.char('a' as u32),
            re.char('b' as u32),
            re.range('0' as u32, '9' as u32),
            re.range('A' as u32, 'Z' as u32),
        ]
    }

    fn build_test_res(re: &mut ReManager) -> Vec<RegLan> {
        let mut v = build_atoms(re);
        let w = v.clone();

        for &x in &w {
            v.push(re.complement(x));
            v.push(re.opt(x));
            v.push(re.star(x));
            v.push(re.plus(x));
            v.push(re.exp(x, 2));
        }
        for &x in &w {
            for &y in &w {
                v.push(re.concat(x, y));
                v.push(re.inter(x, y));
                v.push(re.union(x, y));
            }
        }
        v.sort();
        v.dedup();
        v
    }

    fn check_equal(re1: RegLan, re2: RegLan) {
        assert_eq!(re1, re2);
        assert_eq!(re1.id, re2.id);
        assert!(std::ptr::eq(re1, re2));
    }

    #[test]
    fn hash_atoms() {
        let re = &mut ReManager::new();

        let v1 = build_atoms(re);
        let v2 = build_atoms(re);

        for (i, &t) in v1.iter().enumerate() {
            let name = format!("t{}", i);
            print_term(&name, t);
            check_equal(t, v2[i]);
        }
    }

    #[test]
    fn test_loop() {
        let re = &mut ReManager::new();

        let v = build_atoms(re);

        for &t in &v {
            let x = re.star(t);
            print_term(&format!("star({})", t), x);
            check_equal(x, re.star(t));
        }

        for &t in &v {
            let x = re.plus(t);
            print_term(&format!("plus({})", t), x);
            check_equal(x, re.plus(t));
        }

        for &t in &v {
            let x = re.opt(t);
            print_term(&format!("opt({})", t), x);
            check_equal(x, re.opt(t));
        }

        for &t in &v {
            for k in 0..3 {
                let x = re.exp(t, k);
                print_term(&format!("exp({}, {})", t, k), x);
                check_equal(x, re.exp(t, k));
            }
        }

        let a = re.all_chars();
        let a2 = re.exp(a, 2);
        let a2_star = re.star(a2);
        let a_star = re.star(a);
        let a_plus = re.plus(a);
        let a_star2 = re.exp(a_star, 2);
        let a_star_star = re.star(a_star);
        let a_plus_star = re.star(a_plus);
        let a_star_plus = re.plus(a_star);
        print_term("(Sigma^2)^*", a2_star);
        print_term("(Sigma^*)^2", a_star2);
        print_term("(Sigma^*)^*", a_star_star);
        print_term("(Sigma^*)^+)", a_star_plus);
        print_term("(Sigma^+)^*", a_plus_star);

        assert_eq!(a_star2, a_star);
        assert_ne!(a2_star, a_star);
        assert_eq!(a_plus_star, a_star);
        assert_eq!(a_star_plus, a_star);
        assert_eq!(a_star_star, a_star);
    }

    #[test]
    fn test_concat() {
        let re = &mut ReManager::new();
        let v = build_atoms(re);

        for &t in &v {
            for &u in &v {
                let x = re.concat(t, u);
                print_term(&format!("concat({}, {})", t, u), x);
                check_equal(x, re.concat(t, u));
            }
        }
    }

    #[test]
    fn test_inter() {
        let re = &mut ReManager::new();
        let v = build_atoms(re);

        for &t in &v {
            for &u in &v {
                let x = re.inter(t, u);
                print_term(&format!("inter({}, {})", t, u), x);
                check_equal(x, re.inter(t, u));
            }
        }
    }

    #[test]
    fn test_union() {
        let re = &mut ReManager::new();
        let v = build_atoms(re);

        for &t in &v {
            for &u in &v {
                let x = re.union(t, u);
                print_term(&format!("union({}, {})", t, u), x);
                check_equal(x, re.union(t, u));
            }
        }
    }

    #[test]
    fn test_complement() {
        let re = &mut ReManager::new();
        let v = build_atoms(re);

        for &t in &v {
            let x = re.complement(t);
            print_term(&format!("complement({})", t), x);
            check_equal(x, re.complement(t));

            let y = re.complement(x);
            print_term(&format!("complement({})", x), y);
            check_equal(y, t);
            check_equal(y, re.complement(x));
        }
    }

    #[test]
    fn test_from_str() {
        let re = &mut ReManager::new();

        let x = re.str(&SmtString::from("abcde"));
        print_term("(str.to_re \"abcde\")", x);
        check_equal(x, re.str(&SmtString::from("abcde")));

        let v = vec![
            re.char('a' as u32),
            re.char('b' as u32),
            re.epsilon(),
            re.epsilon(),
            re.char('c' as u32),
            re.char('d' as u32),
            re.char('e' as u32),
        ];

        let y = re.concat_list(v);
        check_equal(x, y);
    }

    #[test]
    fn bigger_test() {
        let re = &mut ReManager::new();
        let v = build_test_res(re);

        for &t in &v {
            for &u in &v {
                let x = re.concat(t, u);
                print_term(&format!("concat({}, {})", t, u), x);
                check_equal(x, re.concat(t, u));

                let x = re.inter(t, u);
                print_term(&format!("inter({}, {})", t, u), x);
                check_equal(x, re.inter(t, u));

                let x = re.union(t, u);
                print_term(&format!("union({}, {})", t, u), x);
                check_equal(x, re.union(t, u));
            }
        }
    }

    #[test]
    fn test_sub_terms() {
        fn print_sub_terms(t: RegLan) {
            println!("Base term: {}", t);
            println!("Sub terms = [");
            for x in sub_terms(t) {
                println!("  {}", x);
            }
            println!("]");

            println!("Leaves = [");
            for leaf in leaves(t) {
                println!("  {}", leaf);
            }
            println!("]\n");
        }

        let re = &mut ReManager::new();
        let v = build_test_res(re);
        for &t in &v {
            print_sub_terms(t)
        }

        let t = re.str(&"0987654321aabd".into());
        print_sub_terms(t)
    }

    #[test]
    fn test_base_patterns() {
        let re = &mut ReManager::new();

        fn show_patterns(r: RegLan) {
            let v = decompose_concat(r);
            let test = base_patterns(&v);
            println!("Expression: {} ", r);
            println!("   vector:");
            for x in &v {
                println!("     {}", x);
            }
            println!("   base patterns:");
            for x in &test {
                println!("     {}", x);
            }
            println!()
        }

        let test1 = re.all_chars();
        show_patterns(test1);

        let test2 = re.epsilon();
        show_patterns(test2);

        let test3 = re.full();
        show_patterns(test3);

        let digits = re.range('0' as u32, '9' as u32);
        let d = re.star(digits);

        let test4 = re.concat_list([test1, digits, test3, test3, d, test1, d, d]);
        show_patterns(test4);
    }

    #[test]
    fn test_deriv() {
        let re = &mut ReManager::new();
        let v = build_test_res(re);

        for &t in &v {
            for c in t.deriv_class.ranges() {
                let x = re.set_derivative(t, c);
                match x {
                    Ok(d) => println!("deriv {} wrt {} = {}", t, c, d),
                    Err(e) => panic!("deriv {} wrt {} failed with error {:?}", t, c, e),
                }
            }
            if !t.deriv_class.empty_complement() {
                let y = re.class_derivative(t, ClassId::Complement);
                match y {
                    Ok(d) => println!("deriv {} wrt CompClass = {}", t, d),
                    Err(e) => panic!("deriv {} wrt CompClass failed with error {:?}", t, e),
                }
            }
        }
    }

    // deriv e w.r.t. 'a', 'b', and 'c' and e's complementary class
    fn show_derivatives(re: &mut ReManager, e: RegLan) {
        println!("Expression: {}", e);
        println!("  deriv classes: {}", e.deriv_class);
        for c in 'a'..='c' {
            println!(
                "  deriv({}, {}) = {}",
                e,
                c,
                re.char_derivative(e, c as u32)
            )
        }
        if !e.empty_complement() {
            println!(
                "  deriv({}, CompClass) = {}",
                e,
                re.class_derivative(e, ClassId::Complement).unwrap()
            )
        }
        println!()
    }

    #[test]
    fn test_deriv2() {
        let re = &mut ReManager::new();
        // a + ac + bc
        let a = re.str(&"a".into());
        let ac = re.str(&"ac".into());
        let bc = re.str(&"bc".into());
        let e = re.union_list([a, ac, bc]);

        show_derivatives(re, e);
        let d1 = re.char_derivative(e, 'a' as u32);
        show_derivatives(re, d1);
        let d2 = re.char_derivative(e, 'b' as u32);
        show_derivatives(re, d2);
        let d3 = re.char_derivative(e, 'c' as u32);
        show_derivatives(re, d3);

        assert!(re.str_in_re(&"a".into(), e));
        assert!(re.str_in_re(&"ac".into(), e));
        assert!(re.str_in_re(&"bc".into(), e));
        assert!(!re.str_in_re(&"b".into(), e));
        assert!(!re.str_in_re(&"c".into(), e));
    }

    #[test]
    fn test_deriv3() {
        let re = &mut ReManager::new();
        // (ac + bc)*
        let ac = re.str(&"ac".into());
        let bc = re.str(&"bc".into());
        let sum = re.union(ac, bc);
        let e = re.star(sum);

        show_derivatives(re, e);
        let d1 = re.char_derivative(e, 'a' as u32);
        show_derivatives(re, d1);
        let d2 = re.char_derivative(e, 'b' as u32);
        show_derivatives(re, d2);
        let d3 = re.char_derivative(e, 'c' as u32);
        show_derivatives(re, d3);

        assert!(re.str_in_re(&"acacbc".into(), e));
        assert!(re.str_in_re(&"".into(), e));
    }

    fn all_derivatives(re: &mut ReManager, e: RegLan) -> Vec<RegLan> {
        let mut queue = BfsQueue::new();
        let mut result = Vec::new();

        queue.push(e);
        result.push(e);

        while let Some(r) = queue.pop() {
            for cid in r.class_ids() {
                if let Ok(d) = re.class_derivative(r, cid) {
                    if queue.push(d) {
                        result.push(d)
                    }
                } else {
                    panic!("Unexpected failure: deriv {} w.r.t Class{}", r, cid)
                }
            }
        }
        result
    }

    #[test]
    fn test_all_deriv() {
        fn show_derivs(e: RegLan, v: &[RegLan]) {
            println!("All derivatives of {}", e);
            for &d in v {
                println!("   {}", d)
            }
            if v.len() == 1 {
                println!("Total: 1 derivative")
            } else {
                println!("Total: {} derivatives", v.len())
            }
        }

        let re = &mut ReManager::new();

        // (ac + bc)*
        let ac = re.str(&"ac".into());
        let bc = re.str(&"bc".into());
        let sum = re.union(ac, bc);
        let e = re.star(sum);

        let v = all_derivatives(re, e);
        show_derivs(e, &v);

        let a = [
            re.sigma_plus(),
            re.str(&"something".into()),
            re.all_chars(),
            re.all_chars(),
            re.char(':' as u32),
            re.full(),
            re.char(':' as u32),
            re.full(),
            re.str(&".jpg".into()),
        ];

        let e = re.concat_list(a);
        let v = all_derivatives(re, e);
        show_derivs(e, &v);
    }

    #[test]
    fn test_derivative_iter() {
        let re = &mut ReManager::new();

        // abc/(Σ^*)/ΣΣ-ΣΣ/def/(Σ^*)
        let a = [
            re.str(&"abc/".into()),
            re.full(),
            re.char('/' as u32),
            re.all_chars(),
            re.all_chars(),
            re.char('-' as u32),
            re.all_chars(),
            re.all_chars(),
            re.str(&"/def/".into()),
            re.full(),
        ];

        let e = re.concat_list(a);
        println!("All derivatives of {}", e);
        let mut count = 0;
        for r in re.iter_derivatives(e) {
            println!("  {}", r);
            count += 1;
        }
        println!("Total: {} derivatives", count);
    }

    #[test]
    fn test_char_deriv() {
        fn sum_of_str(re: &mut ReManager, s1: &str, s2: &str) -> RegLan {
            let s1 = re.str(&s1.into());
            let s2 = re.str(&s2.into());
            re.union(s1, s2)
        }

        let mut re = ReManager::new();
        let e = sum_of_str(&mut re, "abc", "acc");

        // e is 'abc + acc'
        // the derivative of e w.r.t. 'a' is 'bc + cc'
        let d = re.char_derivative(e, 'a' as u32);
        assert_eq!(d, sum_of_str(&mut re, "bc", "cc"));
    }

    #[test]
    fn test_empty_check() {
        let re = &mut ReManager::new();

        let full = re.full();
        let abcd = re.str(&"abcd".into());
        let bc = re.str(&"bc".into());

        let a = re.concat(abcd, full); // strings that start with 'abcd'
        let b = re.concat_list([full, bc, full]); // strings that contain 'bc'

        let test = re.diff(a, b); // strings that start with 'abcd' but don't contain 'bc'
        assert!(re.is_empty_re(test));
    }

    #[test]
    fn test_empty_check2() {
        let re = &mut ReManager::new();

        let c1 = [
            re.all_chars(),
            re.all_chars(),
            re.all_chars(),
            re.all_chars(),
            re.full(),
            re.str(&"/abcd/".into()),
            re.all_chars(),
            re.str(&"/end".into()),
        ];

        let c2 = [re.all_chars(), re.str(&"/zhfg".into()), re.full()];

        let e1 = re.concat_list(c1);
        let e2 = re.concat_list(c2);

        let test = re.inter(e1, e2);
        assert!(!re.is_empty_re(test));

        let sample = re.get_string(test);
        assert!(sample.is_some());
        println!("Sample string in {}: {}", test, sample.unwrap());
    }

    #[test]
    fn test_compile() {
        let re = &mut ReManager::new();

        // (ac + bc)*
        let ac = re.str(&"ac".into());
        let bc = re.str(&"bc".into());
        let sum = re.union(ac, bc);
        let e = re.star(sum);

        // convert e to an automaton
        let auto = re.compile(e);
        println!("Automaton for (ac + bc)*");
        println!("{}", auto);

        println!("Char partition: {}", auto.combined_char_partition());

        let reps = auto.pick_alphabet();
        print!("Alphabet:");
        for x in reps {
            print!(" {}", char_to_smt(x));
        }
        println!();

        let m = auto.compile_successors();
        println!("Compiled transition table: size = {}", m.size());

        assert_eq!(auto.num_states(), 3);
        assert_eq!(auto.num_final_states(), 1);
    }

    #[test]
    fn test_compile2() {
        let re = &mut ReManager::new();

        let a = [
            re.sigma_plus(),
            re.str(&"something".into()),
            re.all_chars(),
            re.all_chars(),
            re.char(':' as u32),
            re.full(),
            re.char(':' as u32),
            re.full(),
            re.str(&".jpg".into()),
        ];

        let e = re.concat_list(a);

        let auto = re.compile(e);
        println!("Automaton for {}", e);
        println!("{}", auto);

        println!("Char partition: {}", auto.combined_char_partition());

        let a = auto.pick_alphabet();
        print!("Alphabet representatives:");
        for x in a {
            print!(" {}", char_to_smt(x));
        }
        println!();

        let m = auto.compile_successors();
        println!("Compiled transition table: size = {}", m.size());
        println!("Transition table: {}", m);

        assert!(auto.accepts(&"prefix_then_somethingAB:middle:mores_stuff.jpg".into()));
        assert!(!auto.accepts(&"prefix_then_something:middle:mores_stuff.jpg".into()));

        auto.test_minimizer();
    }

    #[test]
    fn test_compile3() {
        let re = &mut ReManager::new();

        let c1 = [
            re.all_chars(),
            re.all_chars(),
            re.all_chars(),
            re.all_chars(),
            re.full(),
            re.str(&"/abcd/".into()),
            re.all_chars(),
            re.str(&"/end".into()),
        ];

        let c2 = [re.all_chars(), re.str(&"/zhfg".into()), re.full()];

        let e1 = re.concat_list(c1);
        let e2 = re.concat_list(c2);

        let test = re.inter(e1, e2);

        let auto = re.compile(test);
        println!("Automaton for {}", test);
        println!("{}", auto);

        println!("Char partition: {}", auto.combined_char_partition());
        let a = auto.pick_alphabet();
        print!("Alphabet representatives:");
        for x in a {
            print!(" {}", char_to_smt(x));
        }
        println!();

        let m = auto.compile_successors();
        println!("Compiled transition table: size = {}", m.size());
        println!("Table: {}", m);

        let w = re.get_string(test).unwrap();
        assert!(auto.accepts(&w));

        auto.test_minimizer();
    }

    #[test]
    fn test_bounded_compile() {
        let re = &mut ReManager::new();

        // abc/(Σ^*)/ΣΣ-ΣΣ/def/(Σ^*)
        let a = [
            re.str(&"abc/".into()),
            re.full(),
            re.char('/' as u32),
            re.all_chars(),
            re.all_chars(),
            re.char('-' as u32),
            re.all_chars(),
            re.all_chars(),
            re.str(&"/def/".into()),
            re.full(),
        ];

        let e = re.concat_list(a);

        let test0 = re.try_compile(e, 0);
        assert!(test0.is_none());

        let test1 = re.try_compile(e, 46);
        assert!(test1.is_none());

        let test2 = re.try_compile(e, 47);
        assert!(test2.is_some());
        assert_eq!(test2.unwrap().num_states(), 47);
    }
}
