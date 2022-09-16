// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Regular expressions as defined in the SMT-LIB QF_S Theory
//! The alphabet is the set of u32 between 0 and 0x2FFFF.
//!

use crate::matcher::{naive_re_search, SearchResult};
use crate::regular_expressions::*;
use crate::smt_strings::*;
use std::cell::RefCell;

//
// RegLan and ReManager are not thread safe (because we use Rc not Arc).
// We keep a reference to a global ReManager as a thread-local object.
//
thread_local!(static MANAGER : RefCell<ReManager> = RefCell::new(ReManager::new()));

///
/// Singleton language
///
/// # Example
/// ```
/// use aws_smt_strings::{smt_strings::*, smt_regular_expressions::*};
///
/// let test = SmtString::from("abcde");
/// let re = str_to_re(&test);
/// assert!(str_in_re(&test, re));
/// ```
pub fn str_to_re(s: &SmtString) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().str(s))
}

///
/// Empty language
///
/// # Example
///
/// ```
/// use aws_smt_strings::{smt_strings::*, smt_regular_expressions::*};
///
/// let test = EMPTY;
/// assert!(! str_in_re(&test, re_none()));
/// ```
pub fn re_none() -> RegLan {
    MANAGER.with(|m| m.borrow().empty())
}

///
/// Full language
///
/// # Example
///
/// ```
/// use aws_smt_strings::{smt_strings::*, smt_regular_expressions::*};
///
/// assert!(str_in_re(&EMPTY, re_all()));
/// assert!(str_in_re(&"18938".into(), re_all()));
/// ```
pub fn re_all() -> RegLan {
    MANAGER.with(|m| m.borrow().full())
}

///
/// All strings of length 1
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r = re_allchar();
/// assert!(str_in_re(&"A".into(), r));
/// assert!(! str_in_re(&"AA".into(), r));
/// ```
///
pub fn re_allchar() -> RegLan {
    MANAGER.with(|m| m.borrow_mut().all_chars())
}

///
/// Concatenation of two regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let aaa = str_to_re(&"aaa".into());
/// let bbb = str_to_re(&"bbb".into());
/// assert!(str_in_re(&"aaabbb".into(), re_concat(aaa, bbb)));
/// ```
pub fn re_concat(r1: RegLan, r2: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().concat(r1, r2))
}

///
/// Concatenation of several regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r1 = str_to_re(&"abc".into());
/// let r2 = re_allchar();
/// let c = re_concat_list([r1, r2, r2]);
/// assert!(str_in_re(&"abcXY".into(), c));
/// ```
pub fn re_concat_list(a: impl IntoIterator<Item = RegLan>) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().concat_list(a))
}

///
/// Union of two regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r1 = re_star(str_to_re(&"a".into()));
/// let r2 = re_star(str_to_re(&"b".into()));
/// let u = re_union(r1, r2);
/// assert!(str_in_re(&"aaaa".into(), u));
/// assert!(str_in_re(&"bbb".into(), u));
/// assert!(str_in_re(&"".into(), u));
/// ```
pub fn re_union(r1: RegLan, r2: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().union(r1, r2))
}

///
/// Union of several regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r1 = re_plus(str_to_re(&"a".into()));
/// let r2 = re_plus(str_to_re(&"b".into()));
/// let r3 = re_plus(str_to_re(&"c".into()));
/// let u = re_union_list([r1, r2, r3]);
/// assert!(str_in_re(&"cccc".into(), u));
/// ```
pub fn re_union_list(a: impl IntoIterator<Item = RegLan>) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().union_list(a))
}

///
/// Intersection of two regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r1 = re_star(str_to_re(&"a".into()));
/// let r2 = re_star(str_to_re(&"b".into()));
/// let u = re_inter(r1, r2);
/// assert!(str_in_re(&"".into(), u));
/// assert!(! str_in_re(&"aaa".into(), u));
/// ```
pub fn re_inter(r1: RegLan, r2: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().inter(r1, r2))
}

///
/// Intersection of several regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r1 = re_concat(str_to_re(&"aaaa".into()), re_all());
/// let r2 = re_concat(str_to_re(&"aaa".into()), re_all());
/// let r3 = re_concat(str_to_re(&"aa".into()), re_all());
/// let r = re_inter_list([r1, r2, r3]);
/// assert!(str_in_re(&"aaaabb".into(), r));
/// ```
pub fn re_inter_list(a: impl IntoIterator<Item = RegLan>) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().inter_list(a))
}

///
/// Kleene closure
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r = re_star(re_union(str_to_re(&"aba".into()), str_to_re(&"cc".into())));
/// assert!(str_in_re(&"ccccabacc".into(), r));
/// ```
pub fn re_star(r: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().star(r))
}

///
/// Complement
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r = re_comp(str_to_re(&"abcd".into()));
/// assert!(! str_in_re(&"abcd".into(), r));
/// assert!(str_in_re(&"abcdef".into(), r));
/// ```
pub fn re_comp(r: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().complement(r))
}

///
/// Difference of two regular expressions
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r1 = re_all();
/// let r2 = re_concat(re_allchar(), re_allchar());
/// let r = re_diff(r1, r2);
/// assert!(str_in_re(&"X".into(), r));
/// assert!(str_in_re(&"XYZ".into(), r));
/// ```
///
pub fn re_diff(r1: RegLan, r2: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().diff(r1, r2))
}

///
/// Difference of several languages
///
/// `re_diff_list(r, a)` is the same as `re_diff(r, re_inter_list(a))`
///
pub fn re_diff_list(r: RegLan, a: impl IntoIterator<Item = RegLan>) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().diff_list(r, a))
}

///
/// Kleene cross
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r = re_union(str_to_re(&"ab".into()), str_to_re(&"cde".into()));
/// assert!(str_in_re(&"abcdeab".into(), re_plus(r)));
/// ```
pub fn re_plus(r: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().plus(r))
}

///
/// Option
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let r = str_to_re(&"abcd".into());
/// let opt_r = re_opt(r);
/// assert!(str_in_re(&"".into(), opt_r));
/// assert!(str_in_re(&"abcd".into(), opt_r));
/// ```
pub fn re_opt(r: RegLan) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().opt(r))
}

///
/// Range
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let digit = re_range(&"0".into(), &"9".into());
/// assert!(str_in_re(&"6".into(), digit));
/// ```
///
pub fn re_range(s1: &SmtString, s2: &SmtString) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().smt_range(s1, s2))
}

///
/// Power
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let digit = re_range(&"0".into(), &"9".into());
/// let three_digits = re_power(digit, 3);
/// assert!(str_in_re(&"124".into(), three_digits));
/// ```
pub fn re_power(r: RegLan, k: u32) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().exp(r, k))
}

///
/// Loop
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let digit = re_range(&"0".into(), &"9".into());
/// let two_to_five_digits = re_loop(digit, 2, 5);
/// assert!(str_in_re(&"98".into(), two_to_five_digits));
/// assert!(str_in_re(&"98765".into(), two_to_five_digits));
/// ```
///
pub fn re_loop(r: RegLan, i: u32, j: u32) -> RegLan {
    MANAGER.with(|m| m.borrow_mut().smt_loop(r, i, j))
}

///
/// Check whether a string is in a regular expression
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let any = re_allchar();
/// let all = re_all();
/// let sep = str_to_re(&":".into());
/// let aaa = str_to_re(&"aaa".into());
/// let t = re_concat_list([any, any, sep, aaa, sep, all, sep, aaa, sep, all]);
///
/// assert!(str_in_re(&"ij:aaa::aaa:cdef".into(), t));
/// ```
///
pub fn str_in_re(s: &SmtString, r: RegLan) -> bool {
    MANAGER.with(|m| m.borrow_mut().str_in_re(s, r))
}

///
/// Search for a match of r in s starting at index k
///
fn find_match(r: RegLan, s: &[u32], k: usize, allow_empty: bool) -> SearchResult {
    MANAGER.with(|m| naive_re_search(&mut m.borrow_mut(), r, s, k, allow_empty))
}

///
/// Replace the first and shortest occurrence of r by s2 in s1
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let a_star = re_star(str_to_re(&"a".into()));
/// assert_eq!(str_replace_re(&"baab".into(), a_star, &"cc".into()), "ccbaab".into());
///
/// let a_plus = re_plus(str_to_re(&"a".into()));
/// assert_eq!(str_replace_re(&"baab".into(), a_plus, &"cc".into()), "bccab".into());
///
/// assert_eq!(str_replace_re(&"nomtch".into(), a_plus, &"cc".into()), "nomtch".into());
/// ```
///
pub fn str_replace_re(s1: &SmtString, r: RegLan, s2: &SmtString) -> SmtString {
    let s1 = s1.as_ref();
    match find_match(r, s1, 0, true) {
        SearchResult::NotFound => s1.into(),
        SearchResult::Found(i, j) => {
            let mut x = Vec::new();
            x.extend_from_slice(&s1[..i]);
            x.extend_from_slice(s2.as_ref());
            x.extend_from_slice(&s1[j..]);
            x.into()
        }
    }
}

///
/// Replace all non-empty matches of r by s2 in s1
///
/// # Example
///
/// ```
/// use aws_smt_strings::smt_regular_expressions::*;
///
/// let a_star = re_star(str_to_re(&"a".into()));
/// assert_eq!(str_replace_re_all(&"baab".into(), a_star, &"cd".into()), "bcdcdb".into());
///
/// let digits = re_plus(re_range(&"0".into(), &"9".into()));
/// let pattern = re_concat(str_to_re(&"pre".into()), digits);
/// assert_eq!(str_replace_re_all(&"10pre129prepre0xx".into(), pattern, &"Z".into()),
///            "10Z29preZxx".into());
/// ```
pub fn str_replace_re_all(s1: &SmtString, r: RegLan, s2: &SmtString) -> SmtString {
    let s1 = s1.as_ref();
    let s2 = s2.as_ref();
    let mut x = Vec::new();
    let mut i = 0;
    while let SearchResult::Found(j, k) = find_match(r, s1, i, false) {
        // s[j .. k] == p
        x.extend_from_slice(&s1[i..j]);
        x.extend_from_slice(s2);
        i = k;
    }
    x.extend_from_slice(&s1[i..]);
    x.into()
}
