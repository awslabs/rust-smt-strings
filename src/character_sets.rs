// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Character sets and alphabet partitions
//!
//! An SMT-LIB character is an unsigned integer in the range `[0..MAX_CHAR]`. We represent characters
//! by `u32` integers in this range. The constant [MAX_CHAR] is defined in [smt_strings][crate::smt_strings].
//!
//! A character set is either a single character (e.g., `'A'`) or a range of characters (e.g., `['0'..'9']`).
//! We represent both as `CharSet`s. A `CharSet` is a pair of two integers, `start` and `end`, where
//! `start <= end` and `end <= MAX_CHAR`. This denotes the character interval `[start, end]`.
//!
//! A partition is a collection of disjoint character sets, sorted in increasing order.
//! A partition is then a list of intervals:
//!
//! [a<sub>0</sub>, b<sub>0</sub>], [a<sub>1</sub>, b<sub>1</sub>], ..., [a<sub>k</sub>, b<sub>k</sub>]
//! where a<sub>i</sub> <= b<sub>i</sub> and b<sub>i</sub> < a<sub>i+1</sub>.
//!
//! A partition defines an equivalence relation over characters: two characters are
//! equivalent either if they belong to the same class [a<sub>i</sub>, b<sub>i</sub>] or
//! if they're outside of all the intervals.
//!
//! A partition with n intervals defines then (n+1) classes:
//! C<sub>0</sub>, C<sub>1</sub>, ..., C<sub>n-1</sub> and D.
//! - For i=0,..., n-1, class C<sub>i</sub> is the interval [a<sub>i</sub>, b<sub>i</sub>].
//! - Class D is the complementary class, that is, the complement of Union(C<sub>0</sub>, ..., C<sub>n-1</sub>).
//!
//! Note: the complementary class D may be empty.
//!
//! Each class in a partition can be identified by its [ClassId]:
//! - `ClassId::Interval(i)` denotes the class C<sub>i</sub>, that is, the interval [a<sub>i</sub>, b<sub>i</sub>].
//! - `ClassId::Complement` denotes the complementary class D.
//!
//! Partitions are used to decompose the SMT-LIB alphabet (of 196608 characters) into a typically much smaller number
//! of equivalent classes.
//! - For regular expressions, a partition divides the alphabet into derivative classes.
//!   See [ReManager](crate::regular_expressions::ReManager).
//! - For a finite-state automaton, a partition divides the alphabet into classes that have the
//!   same transitions. A character partition is attached to every state `s` in an automaton and the successors
//!   of `s` are defined for every class in this partition. See [Automaton](crate::automata::Automaton).
//!

use std::{
    cmp::{max, min, Ordering},
    fmt::Display,
};

use crate::{
    errors::Error,
    smt_strings::{char_to_smt, MAX_CHAR},
};

///
/// Interval [start, end] where start <= end <= [MAX_CHAR].
///
/// This represents a range of characters.
///
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct CharSet {
    start: u32,
    end: u32,
}

impl Display for CharSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let a = self.start;
        let b = self.end;
        if a == b {
            write!(f, "{}", char_to_smt(a))
        } else if a == 0 && b == MAX_CHAR {
            write!(f, "\u{03a3}") // Sigma
        } else {
            write!(f, "[{}..{}]", char_to_smt(a), char_to_smt(b))
        }
    }
}

// partial order:
//  [a, b] < [c, d] iff b < c
impl PartialOrd for CharSet {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if self.end < other.start {
            Some(Ordering::Less)
        } else if self.start > other.end {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

impl CharSet {
    /// Construct the singleton interval [x, x]
    ///
    /// - the integer x must be a valid SMT-LIB character (i.e., 0 <= x <= [MAX_CHAR])
    pub fn singleton(x: u32) -> CharSet {
        debug_assert!(x <= MAX_CHAR);
        CharSet { start: x, end: x }
    }

    /// Construct the interval [x, y]
    ///
    /// - requires x <= y <= [MAX_CHAR]
    pub fn range(x: u32, y: u32) -> CharSet {
        debug_assert!(x <= y && y <= MAX_CHAR);
        CharSet { start: x, end: y }
    }

    /// Construct the interval [0, [MAX_CHAR]]
    pub fn all_chars() -> CharSet {
        CharSet {
            start: 0,
            end: MAX_CHAR,
        }
    }

    /// Check whether x is in this interval
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// assert!(c.contains('g' as u32));
    /// assert!(!c.contains('0' as u32));
    /// ```
    pub fn contains(&self, x: u32) -> bool {
        self.start <= x && x <= self.end
    }

    /// Check whether other is a subset of this set
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// assert!(c.covers(&CharSet::singleton('g' as u32)));
    /// assert!(c.covers(&CharSet::range('t' as u32, 'z' as u32)));
    /// assert!(! c.covers(&CharSet::range(0, 'k' as u32)));
    /// ```
    pub fn covers(&self, other: &CharSet) -> bool {
        debug_assert!(other.start <= other.end);
        self.start <= other.start && other.end <= self.end
    }

    /// Check whether this set is before x
    ///
    /// If set is [a, b] this checks whether b < x.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// assert!(c.is_before(127));
    /// assert!(! c.is_before('c' as u32));
    /// ```
    pub fn is_before(&self, x: u32) -> bool {
        self.end < x
    }

    /// Check whether this set is after x
    ///
    /// If set is the interval [a, b], this checks whether x < a.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// assert!(! c.is_after(127));
    /// assert!(c.is_after('Z' as u32));
    /// ```
    pub fn is_after(&self, x: u32) -> bool {
        x < self.start
    }

    /// Get the size of this set
    ///
    /// Return the number of characters in the interval
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// assert_eq!(c.size(), 26);
    /// ```
    pub fn size(&self) -> u32 {
        self.end - self.start + 1
    }

    ///
    /// Check whether the set is a singleton
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// let d = CharSet::singleton('K' as u32);
    /// assert!(d.is_singleton());
    /// assert!(! c.is_singleton());
    /// ```
    pub fn is_singleton(&self) -> bool {
        self.start == self.end
    }

    /// Check whether this set is the full alphabet
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::{character_sets::CharSet, smt_strings::MAX_CHAR};
    ///
    /// let c = CharSet::range(0, MAX_CHAR);
    /// let d = CharSet::range('a' as u32, 'z' as u32);
    /// assert!(c.is_alphabet());
    /// assert!(! d.is_alphabet());
    /// ```
    pub fn is_alphabet(&self) -> bool {
        self.start == 0 && self.end == MAX_CHAR
    }

    /// Pick a character in the set
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// let d = c.pick();
    /// assert!('a' as u32 <= d && d <= 'z' as u32);
    /// ```
    pub fn pick(&self) -> u32 {
        self.start
    }

    /// Intersection of two intervals
    ///
    /// - return None if the intersection is empty
    /// - return Some(charset) otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32); // ['a', 'z']
    /// let d = CharSet::range('t' as u32, 127);  // ['t', 127]
    ///
    /// // the intersection of c and d is ['t', 'z']
    /// assert_eq!(c.inter(&d), Some(CharSet::range('t' as u32, 'z' as u32)));
    /// ```
    pub fn inter(&self, other: &CharSet) -> Option<CharSet> {
        let max_start = max(self.start, other.start);
        let min_end = min(self.end, other.end);
        if max_start <= min_end {
            Some(Self::range(max_start, min_end))
        } else {
            None
        }
    }

    /// Intersection of an array of intervals
    ///
    /// See [inter][Self::inter]
    /// - return None if the intersection is empty
    /// - return Some(c) otherwise
    pub fn inter_list(a: &[CharSet]) -> Option<CharSet> {
        if a.is_empty() {
            Some(Self::all_chars())
        } else {
            let mut result = a[0];
            for s in &a[1..] {
                match result.inter(s) {
                    None => return None,
                    Some(x) => result = x,
                }
            }
            Some(result)
        }
    }

    /// Union of two intervals
    ///
    /// - return None if the union is not an interval
    /// - return Some(c) where c is a CharSet otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::CharSet;
    ///
    /// let c = CharSet::range('a' as u32, 'z' as u32);
    /// let d = CharSet::range('t' as u32, 127);
    /// let e = CharSet::range('0' as u32, '9' as u32);
    ///
    /// assert_eq!(c.union(&d), Some(CharSet::range('a' as u32, 127)));
    /// assert_eq!(c.union(&e), None);
    /// ```
    pub fn union(&self, other: &CharSet) -> Option<CharSet> {
        let max_end = max(self.end, other.end);
        // union([a, b], [c, d]) is an interval if a <= c-1 <= b or c <= a-1 <= d.
        // we treat the case a==c separately to avoid underflow (when a=0 or c=0)
        if self.start == other.start || (self.start < other.start && self.end >= other.start - 1) {
            Some(Self::range(self.start, max_end))
        } else if other.start < self.start && other.end >= self.start - 1 {
            Some(Self::range(other.start, max_end))
        } else {
            None
        }
    }
}

///
/// Class that covers an interval in a [CharPartition]
///
/// A CoverResult identifies the [CharPartition]'s class that contains
/// an interval [a, b] if any.
///
/// For an interval [a, b] and a partition
///  [a<sub>0</sub>, b<sub>0</sub>], ..., [a<sub>n</sub>, b<sub>n</sub>],
/// CoverResult describes three possible outcomes:
/// - `CoveredBy(i)` means that [a, b] is included in class C<sub>i</sub> = [a<sub>i</sub>, b<sub>i</sub>]
/// - `DisjointFromAll` means that [a, b] does not intersect with any [a<sub>i</sub>, b<sub>i</sub>] so
///   [a, b] is included in the complementary class.
/// - `Overlaps` means that [a, b] and some interval [a<sub>i</sub>, b<sub>i</sub>] intersect,
///   but [a, b] is not contained in this internal.
///
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum CoverResult {
    /// CoveredBy(i) denotes the i-th interval [a<sub>i</sub>, b<sub>i</sub>] in the partition
    CoveredBy(usize),
    /// DisjointFromAll denotes the partition's complementary class
    DisjointFromAll,
    /// Overlaps means that [a, b] intersects some interval [a<sub>i</sub>, b<sub>i</sub>]
    /// but is not fully included in this interval.
    Overlaps,
}

impl Display for CoverResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoverResult::CoveredBy(i) => write!(f, "CoveredBy({i})"),
            CoverResult::DisjointFromAll => write!(f, "DisjointFromAll"),
            CoverResult::Overlaps => write!(f, "Overlaps"),
        }
    }
}

/// ClassId
///
/// A class id identifies a character class defined by a partition.
/// It can either be Interval(i) where i is an index between 0 and the partition length-1 or
/// Complement.
/// - Interval(i) denotes the i-th interval in a partition
/// - Complement denotes the complementary class (not an interval in general)
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum ClassId {
    /// Id of a partition interval
    Interval(usize),
    /// Id of the complementary partition
    Complement,
}

impl Display for ClassId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClassId::Interval(i) => write!(f, "Interval({i})"),
            ClassId::Complement => write!(f, "Complement"),
        }
    }
}

///
/// Collection of disjoint character sets.
///
/// Each character set is an interval [a, b] where a <= b.
///
/// The character sets are sorted in increasing order so a
/// partition of length n is a sequence
///
/// [a<sub>0</sub>, b<sub>0</sub>], [a<sub>1</sub>, b<sub>1</sub>], ..., [a<sub>n-1</sub>, b<sub>n-1</sub>]
/// where a<sub>i</sub> <= b<sub>i</sub> and b<sub>i</sub> < a<sub>i+1</sub>.
///
/// This divides the alphabet into n+1 classes C<sub>0</sub>, ..., C<sub>n-1</sub>, and D:
/// - C<sub>i</sub> = { x | a<sub>i</sub> <= x <= b<sub>i</sub> }
/// - D = complement of Union(C<sub>0</sub>, ..., C<sub>n-1</sub>)
///
/// Each class in a partition can be identified by its [ClassId]:
/// - `ClassId::Interval(i)` denotes the class C<sub>i</sub>, that is, the interval [a<sub>i</sub>, b<sub>i</sub>].
/// - `ClassId::Complement` denotes the complementary class D.
//
// The partition structure includes an integer comp_witness, which is the smallest integer that doesn't
// belong to any of the intervals C<sub>i</sub>. So if comp_witness <= [MAX_CHAR], it's an element of
// the complementary class. Otherwise, comp_witness = [MAX_CHAR]+1 and the complementary class is empty.
//
#[derive(Debug, PartialEq, Eq, Default, Clone)]
pub struct CharPartition {
    list: Vec<CharSet>,
    comp_witness: u32,
}

impl CharPartition {
    /// Number of intervals in the partition
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Check whether the partition is empty (i.e., no intervals)
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Create an empty partition
    pub fn new() -> Self {
        CharPartition::default()
    }

    /// Partition with a single character set
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// let p = CharPartition::from_set(&CharSet::range('a' as u32, 'b' as u32));
    /// assert_eq!(p.len(), 1);
    /// assert_eq!(p.get(0), ('a' as u32, 'b' as u32))
    /// ```
    pub fn from_set(c: &CharSet) -> Self {
        let witness = if c.start > 0 { 0 } else { c.end + 1 };
        CharPartition {
            list: vec![*c],
            comp_witness: witness,
        }
    }

    /// Build a partition from a CharSet iterator
    ///
    /// Succeeds if the CharSets are pairwise disjoint.
    /// Fails otherwise.
    ///
    /// # Errors
    ///
    /// If some CharSets have a non-empty intersection,
    /// return Err([Error::NonDisjointCharSets]).
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let v = [
    ///     CharSet::range(120, 400),
    ///     CharSet::range(0, 10),
    ///     CharSet::range(1000, 2000)];
    ///
    /// let p = CharPartition::try_from_iter(v.into_iter().copied())?;
    /// assert_eq!(p.len(), 3);
    /// assert_eq!(p.get(0), (0, 10));
    /// assert_eq!(p.get(1), (120, 400));
    /// assert_eq!(p.get(2), (1000, 2000));
    /// # Ok(())
    /// # }
    /// ```
    pub fn try_from_iter(iter: impl Iterator<Item = CharSet>) -> Result<Self, Error> {
        let mut v: Vec<CharSet> = iter.collect();
        let mut comp_witness = 0;
        if !v.is_empty() {
            v.sort_by_key(|c| c.start);
            let mut prev = &v[0];
            if prev.start <= comp_witness {
                comp_witness = prev.end + 1;
            }
            for c in &v[1..] {
                if c.start <= prev.end {
                    return Err(Error::NonDisjointCharSets);
                }
                if c.start <= comp_witness {
                    comp_witness = c.end + 1;
                }
                prev = c;
            }
        }
        Ok(CharPartition {
            list: v,
            comp_witness,
        })
    }

    /// Build a partition from a list of CharSets
    ///
    /// Succeeds if the CharSets in `a` are pairwise disjoint.
    /// Fails otherwise.
    ///
    /// # Errors
    ///
    /// If some elements of `a` have a non-empty intersection,
    /// return Err([Error::NonDisjointCharSets]).
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// let v = [
    ///     CharSet::range(120, 400),
    ///     CharSet::range(0, 10),
    ///     CharSet::range(1000, 2000)];
    ///
    /// let p = CharPartition::try_from_list(&v)?;
    /// assert_eq!(p.len(), 3);
    /// assert_eq!(p.get(0), (0, 10));
    /// assert_eq!(p.get(1), (120, 400));
    /// assert_eq!(p.get(2), (1000, 2000));
    ///
    /// # Ok(())
    /// # }
    /// ```
    ///
    pub fn try_from_list(a: &[CharSet]) -> Result<Self, Error> {
        Self::try_from_iter(a.iter().copied())
    }

    /// Add the interval [start, end] at the end of the partition.
    ///
    /// Requires `start <= end` and `end <= MAX_CHAR`.
    /// If the partition is not empty, `start` must also be larger than the end of the
    /// last interval in the partition.
    ///
    /// # Example
    /// This constructs the two-interval partition `['0', '9'] ['Z', 'Z']`.
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// let mut p = CharPartition::new();
    /// p.push('0' as u32, '9' as u32);
    /// p.push('Z' as u32, 'Z' as u32);
    ///
    /// assert_eq!(p.len(), 2);
    /// assert_eq!(p.get(0), ('0' as u32, '9' as u32));
    /// assert_eq!(p.get(1), ('Z' as u32, 'Z' as u32));
    /// ```
    pub fn push(&mut self, start: u32, end: u32) {
        debug_assert!(start <= end && end <= MAX_CHAR);
        debug_assert!(self.list.is_empty() || start > self.list.last().unwrap().end);
        self.list.push(CharSet { start, end });
        if start <= self.comp_witness {
            self.comp_witness = end + 1;
        }
    }

    /// Get the pair (start, end) of the i-the interval in the partition
    ///
    /// Intervals are indexed from 0 to `p.len() - 1` (inclusive).
    /// - if i < p.len(), return the start and end of the i-th interval.
    /// - if i >= p.len(), return the pair  `(MAX_CHAR+1, MAX_CHAR+1)`
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    /// use aws_smt_strings::smt_strings::MAX_CHAR;
    ///
    /// // partition ['0', '9'] ['Z', 'Z']
    /// let mut p = CharPartition::new();
    /// p.push('0' as u32, '9' as u32);
    /// p.push('Z' as u32, 'Z' as u32);
    ///
    /// assert_eq!(p.get(0), ('0' as u32, '9' as u32)); // first interval
    /// assert_eq!(p.get(3), (MAX_CHAR + 1, MAX_CHAR + 1)); // out-of-range index
    /// ```
    pub fn get(&self, i: usize) -> (u32, u32) {
        if i < self.list.len() {
            let r = &self.list[i];
            (r.start, r.end)
        } else {
            (MAX_CHAR + 1, MAX_CHAR + 1)
        }
    }

    /// Get the i-the interval in the partition as a CharSet.
    ///
    /// # Panics
    ///
    /// If i is out of bound, that is, if i >= number of intervals in the partition.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// let mut p = CharPartition::new();
    /// p.push('a' as u32, 'z' as u32);
    ///
    /// assert_eq!(p.interval(0), CharSet::range('a' as u32, 'z' as u32));
    /// ```
    pub fn interval(&self, i: usize) -> CharSet {
        self.list[i]
    }

    /// Get the start of the i-th interval
    ///
    /// - return `MAX_CHAR+1` if i is out of bound.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    /// use aws_smt_strings::smt_strings::MAX_CHAR;
    ///
    /// let mut p = CharPartition::new();
    /// p.push('a' as u32, 'z' as u32);
    ///
    /// assert_eq!(p.start(0), 'a' as u32);
    /// assert_eq!(p.start(1), MAX_CHAR+1);
    /// ```
    pub fn start(&self, i: usize) -> u32 {
        if i < self.len() {
            self.list[i].start
        } else {
            MAX_CHAR + 1
        }
    }

    /// Get the end of the i-th interval
    ///
    /// - return `MAX_CHAR+1` if i is out of bound
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    /// use aws_smt_strings::smt_strings::MAX_CHAR;
    ///
    /// let mut p = CharPartition::new();
    /// p.push('a' as u32, 'z' as u32);
    ///
    /// assert_eq!(p.end(0), 'z' as u32);
    /// assert_eq!(p.end(1), MAX_CHAR+1);
    /// ```
    pub fn end(&self, index: usize) -> u32 {
        if index < self.len() {
            self.list[index].end
        } else {
            MAX_CHAR + 1
        }
    }

    /// Pick an element in interval i
    ///
    /// # Panics
    ///
    /// if i >= number of intervals in the partition
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// let mut p = CharPartition::new();
    /// p.push('a' as u32, 'z' as u32);
    ///
    /// assert!('a' as u32 <= p.pick(0) && p.pick(0) <= 'z' as u32);
    /// ```
    pub fn pick(&self, i: usize) -> u32 {
        self.list[i].start
    }

    /// Check whether the complementary class is empty
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    /// use aws_smt_strings::smt_strings::MAX_CHAR;
    ///
    /// let mut p = CharPartition::new();
    /// p.push(0, 127);
    /// assert!(! p.empty_complement());
    /// p.push(128, MAX_CHAR);
    /// assert!(p.empty_complement());
    /// ```
    pub fn empty_complement(&self) -> bool {
        self.comp_witness > MAX_CHAR
    }

    /// Pick an element in the complementary class
    ///
    /// - return `MAX_CHAR+1` if the complementary class is empty
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    /// use aws_smt_strings::smt_strings::MAX_CHAR;
    ///
    /// // partition with a single interval ['a', 'z']
    /// let p = CharPartition::from_set(&CharSet::range('a' as u32, 'z' as u32));
    ///
    /// // the complementary class is the union of [0, 'a' - 1] and ['z' + 1, MAX_CHAR]
    /// let x = p.pick_complement();
    /// assert!(x < ('a' as u32) || ('z' as u32) < x && x <= MAX_CHAR);
    /// ```
    pub fn pick_complement(&self) -> u32 {
        self.comp_witness
    }

    /// Check whether a class id is valid
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// // partition with two intervals and three classes
    /// let mut p = CharPartition::new();
    /// p.push('0' as u32, '9' as u32);
    /// p.push('Z' as u32, 'Z' as u32);
    ///
    /// assert!(p.valid_class_id(ClassId::Interval(0)));
    /// assert!(p.valid_class_id(ClassId::Interval(1)));
    /// assert!(p.valid_class_id(ClassId::Complement));
    ///
    /// assert!(! p.valid_class_id(ClassId::Interval(2)));
    /// ```
    pub fn valid_class_id(&self, cid: ClassId) -> bool {
        use ClassId::*;
        match cid {
            Interval(i) => i < self.len(),
            Complement => !self.empty_complement(),
        }
    }

    /// Number of classes
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// // partition with two intervals and three classes
    /// let mut p = CharPartition::new();
    /// p.push('0' as u32, '9' as u32);
    /// p.push('Z' as u32, 'Z' as u32);
    ///
    /// assert_eq!(p.num_classes(), 3);
    /// ```
    pub fn num_classes(&self) -> usize {
        let n = self.len();
        if self.empty_complement() {
            n
        } else {
            n + 1
        }
    }

    /// Pick an element in a class
    ///
    /// - cid identifies the class: if cid = Interval(i) then pick in the i-th interval of p
    ///   (intervals are indexed from 0 to p.len() - 1)
    /// - if cid is Complement then pick in the complementary class
    ///
    /// # Panics
    ///
    /// If cid is Interval(i) and i >= p.len() or cid is Complement and the complementary class
    /// is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::{ClassId::*, *};
    /// use aws_smt_strings::smt_strings::MAX_CHAR;
    ///
    /// let mut p = CharPartition::new();
    /// p.push('0' as u32, '9' as u32);
    /// p.push('Z' as u32, 'Z' as u32);
    ///
    /// let x = p.pick_in_class(Interval(1));
    /// assert_eq!(x, 'Z' as u32); // since interval 1 is ['Z', 'Z']
    ///
    /// let y = p.pick_in_class(Complement);
    /// assert!(0 <= y && y < ('0' as u32) ||
    ///         ('9' as u32) < y && y < ('Z' as u32) ||
    ///         ('Z' as u32) < y && y <= MAX_CHAR);
    /// ```
    pub fn pick_in_class(&self, cid: ClassId) -> u32 {
        use ClassId::*;
        match cid {
            Interval(i) => self.pick(i),
            Complement => {
                assert!(!self.empty_complement());
                self.pick_complement()
            }
        }
    }

    /// Iterator to go through all intervals in the partition
    pub fn ranges(&self) -> impl Iterator<Item = &CharSet> {
        self.list.iter()
    }

    /// Iterator to go through all valid class ids
    pub fn class_ids(&self) -> ClassIdIterator<'_> {
        ClassIdIterator {
            partition: self,
            counter: 0,
        }
    }

    /// Iterator to pick one character in each class
    /// (including the complementary class).
    pub fn picks(&self) -> PickIterator<'_> {
        PickIterator {
            partition: self,
            counter: 0,
        }
    }

    ///
    /// Search for the class that contains a character
    ///
    /// - Return `Interval(i)` if `a_i <= x <= b_i`
    /// - Return `Complement` if x is not in any interval
    ///
    pub fn class_of_char(&self, x: u32) -> ClassId {
        #[allow(clippy::many_single_char_names)]
        fn binary_search(p: &[CharSet], x: u32) -> ClassId {
            let mut i = 0;
            let mut j = p.len();
            while i < j {
                let h = i + (j - i) / 2;
                if p[h].contains(x) {
                    return ClassId::Interval(h);
                }
                if p[h].is_before(x) {
                    i = h + 1;
                } else {
                    j = h;
                }
            }
            ClassId::Complement
        }

        binary_search(&self.list, x)
    }

    ///
    /// Search for an interval that covers a character set
    ///
    /// The character set is an interval [a, b] where `0 <= a <= b <= MAX_CHAR`.
    /// - Return `CoverResult::CoveredBy(i)` if [a, b] is included in the i-th
    ///   interval of the partition.
    /// - Return `CoverResult::DisjointFromAll` if [a, b] does not overlap any
    ///   interval in the partition.
    /// - Return `CoverResult::Overlaps` if [a, b] overlaps some interval in
    ///   the partition but it not contained in this interval.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// let p = CharPartition::from_set(&CharSet::range('0' as u32, '9' as u32));
    /// let test1 = CharSet::range('4' as u32, '8' as u32);
    /// let test2 = CharSet::range('a' as u32, 'z' as u32);
    /// let test3 = CharSet::range('5' as u32, '?' as u32);
    ///
    /// assert_eq!(p.interval_cover(&test1), CoverResult::CoveredBy(0));
    /// assert_eq!(p.interval_cover(&test2), CoverResult::DisjointFromAll);
    /// assert_eq!(p.interval_cover(&test3), CoverResult::Overlaps);
    /// ```
    pub fn interval_cover(&self, set: &CharSet) -> CoverResult {
        // search for the largest i such that a_i <= x
        // return 0 if there's no such i (either because p is empty
        // or because x < a_0)
        #[allow(clippy::many_single_char_names)]
        fn binary_search(p: &[CharSet], x: u32) -> usize {
            let mut i = 0;
            let mut j = p.len();
            while i + 1 < j {
                let h = i + (j - i) / 2;
                if p[h].start <= x {
                    i = h
                } else {
                    j = h
                }
            }
            i
        }

        let a = set.start;
        let b = set.end;
        debug_assert!(a <= b && b <= MAX_CHAR);

        let i = binary_search(&self.list, a);
        let (a_i, b_i) = self.get(i);

        if a < a_i {
            debug_assert!(i == 0);
            if b < a_i {
                // a <= b < a_0
                CoverResult::DisjointFromAll
            } else {
                // a < a_0 <= b
                CoverResult::Overlaps
            }
        } else if a <= b_i {
            if b <= b_i {
                // a_i <= a <= b <= b_i
                CoverResult::CoveredBy(i)
            } else {
                // a_i <= a <= b_i < b
                CoverResult::Overlaps
            }
        } else {
            // note: we know i < p.len() <= MAX_CHAR so i+1 can't overflow here
            let next_ai = self.end(i + 1);
            if b < next_ai {
                // a_i <= b_i < a <= b < a_{i+1}
                CoverResult::DisjointFromAll
            } else {
                // a_i <= b_i < a < a_{i+1} <= b
                CoverResult::Overlaps
            }
        }
    }

    /// Get the class id for a character set
    ///
    /// - The class id is Interval(i) if the set is covered by interval
    ///   [a<sub>i</sub>, b<sub>i</sub>] of the partition
    /// - The class id is Complement if the set is covered by the partition's
    ///   complementary class
    /// - Otherwise, the class id is not defined.
    ///
    /// # Error
    ///
    /// If the class id is not defined for s, return Err([Error::AmbiguousCharSet])
    ///
    pub fn class_of_set(&self, s: &CharSet) -> Result<ClassId, Error> {
        use ClassId::*;
        use CoverResult::*;

        match self.interval_cover(s) {
            CoveredBy(i) => Ok(Interval(i)),
            DisjointFromAll => Ok(Complement),
            Overlaps => Err(Error::AmbiguousCharSet),
        }
    }

    /// Check whether character set c is consistent with the partition.
    ///
    /// - return true if c is included in one partition's class or if
    ///   c is included in the partition's complementary class.
    ///
    /// # Example
    ///
    /// ```
    /// use aws_smt_strings::character_sets::*;
    ///
    /// let p = CharPartition::from_set(&CharSet::range('0' as u32, '9' as u32));
    /// let test1 = CharSet::range('4' as u32, '8' as u32);
    /// let test2 = CharSet::range('a' as u32, 'z' as u32);
    /// let test3 = CharSet::range('5' as u32, '?' as u32);
    ///
    /// assert!(p.good_char_set(&test1));
    /// assert!(p.good_char_set(&test2));
    /// assert!(! p.good_char_set(&test3));
    /// ```
    pub fn good_char_set(&self, c: &CharSet) -> bool {
        !matches!(self.interval_cover(c), CoverResult::Overlaps)
    }
}

impl Display for CharPartition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ ")?;
        for r in self.ranges() {
            write!(f, "{r} ")?;
        }
        write!(f, "}}")
    }
}

/// Iterator to go through all valid ClassId's in a partition
#[derive(Debug)]
pub struct ClassIdIterator<'a> {
    partition: &'a CharPartition,
    counter: usize,
}

impl<'a> Iterator for ClassIdIterator<'a> {
    type Item = ClassId;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.counter;
        self.counter += 1;
        if i < self.partition.len() {
            Some(ClassId::Interval(i))
        } else if i == self.partition.len() && !self.partition.empty_complement() {
            Some(ClassId::Complement)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut size = self.partition.len();
        if !self.partition.empty_complement() {
            size += 1;
        }
        (size, Some(size))
    }
}

/// Iterator to pick a character in each class of a partition
///
/// If the partition consists of `n` intervals, the iterator will
/// pick an element in each interval first, then it will pick an
/// element in the complementary partition if this complementary
/// partition is not empty.
///
#[derive(Debug)]
pub struct PickIterator<'a> {
    partition: &'a CharPartition,
    counter: usize,
}

impl<'a> Iterator for PickIterator<'a> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        let i = self.counter;
        self.counter += 1;
        if i < self.partition.len() {
            Some(self.partition.pick(i))
        } else if i == self.partition.len() && !self.partition.empty_complement() {
            Some(self.partition.pick_complement())
        } else {
            None
        }
    }
}

///
/// Merge two partitions p1 and p2
///
/// The result is the coarsest partition p that is a refinement of both p1 and p2.
/// This means that every interval of p1 and every interval of p2 is the union
/// of one or more successive intervals of p.
///
/// More precisely:
/// - let p1 = [a<sub>0</sub>, b<sub>0</sub>], ..., [a<sub>n</sub>, b<sub>n</sub>]
/// - let p2 = [c<sub>0</sub>, d<sub>0</sub>], ..., [c<sub>m</sub>, d<sub>m</sub>]
/// - let D1 = complement(Union [a<sub>i</sub>, b<sub>i</sub>])
/// - let D2 = complement(Union [c<sub>j</sub>, d<sub>j</sub>])
///
/// Then every interval of p is of one of the following forms
/// 1) [a<sub>i</sub>, b<sub>i</sub>] inter D2
/// 2) D1 inter [c<sub>j</sub>, d<sub>j</sub>]
/// 3) [a<sub>i</sub>, b<sub>j</sub>] inter [c<sub>j</sub>, d<sub>j</sub>]
///
/// where 0 <= i <= n and 0 <= j <= m.
///
/// # Example
///
/// ```
/// use aws_smt_strings::character_sets::*;
///
/// // partition p with intervals ['0', '9'] and ['a', 'g']
/// let mut p = CharPartition::new();
/// p.push('0' as u32, '9' as u32);
/// p.push('a' as u32, 'g' as u32);
///
/// // partition q with intervals ['5', '5'] and ['c', 'z']
/// let mut q = CharPartition::new();
/// q.push('5' as u32, '5' as u32);
/// q.push('c' as u32, 'z' as u32);
///
/// // r = merge(p, q) contains six intervals
/// // r = ['0', '4'] ['5', '5'] ['6', '9'] ['a', 'b'] ['c', 'g'] ['h', 'z']
/// let r = merge_partitions(&p, &q);
///
/// assert_eq!(r.len(), 6);
/// assert_eq!(r.get(0), ('0' as u32, '4' as u32));
/// assert_eq!(r.get(1), ('5' as u32, '5' as u32));
/// assert_eq!(r.get(2), ('6' as u32, '9' as u32));
/// assert_eq!(r.get(3), ('a' as u32, 'b' as u32));
/// assert_eq!(r.get(4), ('c' as u32, 'g' as u32));
/// assert_eq!(r.get(5), ('h' as u32, 'z' as u32));
/// ```
#[allow(clippy::many_single_char_names)]
pub fn merge_partitions(p1: &CharPartition, p2: &CharPartition) -> CharPartition {
    // consume interval i of p as [a, b]
    fn next_interval(p: &CharPartition, i: usize) -> (usize, u32, u32) {
        let (x, y) = p.get(i);
        (i + 1, x, y)
    }

    let mut triple1 = next_interval(p1, 0);
    let mut triple2 = next_interval(p2, 0);

    let mut result = CharPartition::new();
    while triple1.2 <= MAX_CHAR || triple2.2 <= MAX_CHAR {
        let (i, a, b) = triple1;
        let (j, c, d) = triple2;
        // [a, b] is a sub-range of the i-th interval of p1
        // [c, d] is a sub-range of the j-th interval of p2
        if b < c {
            // [a, b] < [c, d]
            result.push(a, b);
            triple1 = next_interval(p1, i);
        } else if d < a {
            // [c, d] < [a, b]
            result.push(c, d);
            triple2 = next_interval(p2, j);
        } else if c < a {
            // [c, d] and [a, b] overlap and c<a
            result.push(c, a - 1);
            triple2.1 = a; // next interval in p2 is [a, d]
        } else if a < c {
            // [c, d] and [a, b] overlap and a<c
            result.push(a, c - 1);
            triple1.1 = c; // next interval in p1 is [c, b]
        } else if b < d {
            // a=c and b<d: [a, b] is a prefix of [c, d]
            result.push(a, b);
            triple1 = next_interval(p1, i);
            triple2.1 = b + 1;
        } else if d < b {
            // a=c and d<b: [c, d] is a prefix of [a, b]
            result.push(c, d);
            triple1.1 = d + 1;
            triple2 = next_interval(p2, j);
        } else {
            // a=c and b=d
            result.push(a, b);
            triple1 = next_interval(p1, i);
            triple2 = next_interval(p2, j);
        }
    }
    result
}

///
/// Merge a list of partitions
///
/// See [merge_partitions]
pub fn merge_partition_list<'a>(list: impl Iterator<Item = &'a CharPartition>) -> CharPartition {
    let mut result = CharPartition::new();
    for p in list {
        result = merge_partitions(&result, p)
    }
    result
}

#[cfg(test)]
mod test {
    use super::*;

    fn good_partition(p: &CharPartition) -> bool {
        let mut prev_end = MAX_CHAR + 1;
        for s in p.ranges() {
            if s.start > s.end {
                return false;
            }
            if prev_end <= MAX_CHAR && s.start <= prev_end {
                return false;
            }
            if s.start <= p.comp_witness && p.comp_witness <= s.end {
                return false;
            }
            prev_end = s.end;
        }
        true
    }

    fn example1() -> CharPartition {
        let mut p = CharPartition::new();
        p.push('0' as u32, '9' as u32);
        p.push('Z' as u32, 'Z' as u32);
        p.push('f' as u32, 'q' as u32);
        p
    }

    fn example2() -> CharPartition {
        let mut p = CharPartition::new();
        p.push('0' as u32, '0' as u32);
        p.push('A' as u32, 'G' as u32);
        p.push('H' as u32, 'M' as u32);
        p.push('W' as u32, 'Z' as u32);
        p.push('a' as u32, 'n' as u32);
        p.push('q' as u32, 'r' as u32);
        p
    }

    #[test]
    fn test_simple() {
        let p1 = CharPartition::new();
        let p2 = example1();
        let p3 = example1();
        let p4 = example2();
        let p5 = CharPartition::from_set(&CharSet::all_chars());

        assert!(good_partition(&p1));
        assert!(good_partition(&p2));
        assert!(good_partition(&p4));
        assert!(good_partition(&p5));

        assert!(!p1.empty_complement());
        assert!(p1.pick_complement() == 0);
        assert!(!p2.empty_complement());
        assert!(p2.pick_complement() == 0);
        assert!(!p4.empty_complement());
        assert!(p4.pick_complement() == 0);
        assert!(p5.empty_complement());

        assert_eq!(&p2, &p3);
        assert_ne!(&p2, &p4);
        assert_ne!(&p1, &p2);
        assert_ne!(&p1, &p4);
        assert_ne!(&p1, &p5);

        println!("Empty partition: {}", &p1);
        println!("Example1: {}", &p2);
        println!("Example2: {}", &p4);
        println!("All chars: {}", &p5);
    }

    #[test]
    fn test_from_list() {
        let v = [
            CharSet::range(120, 400),
            CharSet::range(0, 10),
            CharSet::range(1000, 2000),
        ];

        match CharPartition::try_from_list(&v) {
            Ok(p) => {
                println!("From list succeeded: {}", &p);
                assert_eq!(p.len(), 3);
                assert_eq!(p.get(0), (0, 10));
                assert_eq!(p.get(1), (120, 400));
                assert_eq!(p.get(2), (1000, 2000));
                assert!(good_partition(&p));
            }
            Err(e) => panic!("Partition::try_from_list failed with error {}", e),
        }

        let w = [
            CharSet::range(120, 400),
            CharSet::range(1000, 2000),
            CharSet::range(0, 10),
            CharSet::range(100, 200),
        ];

        match CharPartition::try_from_list(&w) {
            Ok(_) => panic!("Partition::try_from_list should have failed"),
            Err(e) => println!("Partition::try_from_list failed with error {e} as expected"),
        }
    }

    #[test]
    fn test_search() {
        use super::ClassId::*;

        let p = CharPartition::new();

        assert_eq!(p.class_of_char('a' as u32), Complement);
        assert_eq!(p.class_of_char(0), Complement);
        assert_eq!(p.class_of_char(MAX_CHAR), Complement);

        let p2 = example1();

        assert_eq!(p2.class_of_char(10), Complement);
        assert_eq!(p2.class_of_char('0' as u32), Interval(0));
        assert_eq!(p2.class_of_char('5' as u32), Interval(0));
        assert_eq!(p2.class_of_char('9' as u32), Interval(0));
        assert_eq!(p2.class_of_char('A' as u32), Complement);
        assert_eq!(p2.class_of_char('Z' as u32), Interval(1));
        assert_eq!(p2.class_of_char('e' as u32), Complement);
        assert_eq!(p2.class_of_char('g' as u32), Interval(2));
        assert_eq!(p2.class_of_char('z' as u32), Complement);

        let p3 = example2();
        assert_eq!(p3.class_of_char(10), Complement);
        assert_eq!(p3.class_of_char('0' as u32), Interval(0));
        assert_eq!(p3.class_of_char('5' as u32), Complement);
        assert_eq!(p3.class_of_char('9' as u32), Complement);
        assert_eq!(p3.class_of_char('A' as u32), Interval(1));
        assert_eq!(p3.class_of_char('F' as u32), Interval(1));
        assert_eq!(p3.class_of_char('G' as u32), Interval(1));
        assert_eq!(p3.class_of_char('H' as u32), Interval(2));
        assert_eq!(p3.class_of_char('L' as u32), Interval(2));
        assert_eq!(p3.class_of_char('O' as u32), Complement);
        assert_eq!(p3.class_of_char('W' as u32), Interval(3));
        assert_eq!(p3.class_of_char('Z' as u32), Interval(3));
        assert_eq!(p3.class_of_char('^' as u32), Complement);
        assert_eq!(p3.class_of_char('e' as u32), Interval(4));
        assert_eq!(p3.class_of_char('g' as u32), Interval(4));
        assert_eq!(p3.class_of_char('p' as u32), Complement);
        assert_eq!(p3.class_of_char('q' as u32), Interval(5));
        assert_eq!(p3.class_of_char('r' as u32), Interval(5));
        assert_eq!(p3.class_of_char('s' as u32), Complement);
        assert_eq!(p3.class_of_char('z' as u32), Complement);

        let p4 = CharPartition::from_set(&CharSet::all_chars());
        assert_eq!(p4.class_of_char(0), Interval(0));
        assert_eq!(p4.class_of_char(MAX_CHAR), Interval(0));
    }

    #[test]
    fn test_merge() {
        let v = vec![CharPartition::new(), example1(), example2()];

        for p in &v {
            for q in &v {
                let m = merge_partitions(p, q);
                println!("Merge({}, {}) = {}", p, q, &m);

                assert!(good_partition(&m));

                if p.is_empty() {
                    assert_eq!(&m, q);
                }
                if q.is_empty() {
                    assert_eq!(&m, p);
                }
                if p == q {
                    assert_eq!(&m, p);
                }
            }
        }
    }

    #[test]
    fn test_inter() {
        let a = CharSet::singleton(0);
        let b = CharSet::range(1, 20);
        let c = CharSet::range(30, 60);
        let d = CharSet::range(0, 30);

        assert_eq!(a.inter(&a), Some(a));
        assert_eq!(a.inter(&b), None);
        assert_eq!(a.inter(&c), None);
        assert_eq!(a.inter(&d), Some(a));

        assert_eq!(b.inter(&a), None);
        assert_eq!(b.inter(&b), Some(b));
        assert_eq!(b.inter(&c), None);
        assert_eq!(b.inter(&d), Some(b));

        assert_eq!(c.inter(&d), Some(CharSet::singleton(30)));
    }

    #[test]
    fn test_union() {
        let a = CharSet::singleton(0);
        let b = CharSet::range(1, 20);
        let c = CharSet::range(30, 60);
        let d = CharSet::range(0, 30);

        assert_eq!(a.union(&a), Some(a));
        assert_eq!(a.union(&b), Some(CharSet::range(0, 20)));
        assert_eq!(a.union(&c), None);
        assert_eq!(a.union(&d), Some(d));

        assert_eq!(b.union(&a), Some(CharSet::range(0, 20)));
        assert_eq!(b.union(&b), Some(b));
        assert_eq!(b.union(&c), None);
        assert_eq!(b.union(&d), Some(d));

        assert_eq!(c.union(&d), Some(CharSet::range(0, 60)));
    }

    #[test]
    fn test_cover() {
        let v = vec![CharPartition::new(), example1(), example2()];
        let i = vec![
            CharSet::singleton('a' as u32),
            CharSet::range('0' as u32, '9' as u32),
            CharSet::range('a' as u32, 'z' as u32),
            CharSet::range('h' as u32, 'q' as u32),
            CharSet::singleton('f' as u32),
            CharSet::singleton('q' as u32),
            CharSet::all_chars(),
            CharSet::singleton(0),
            CharSet::singleton(MAX_CHAR),
            CharSet::range(0, 'z' as u32),
            CharSet::range('z' as u32, MAX_CHAR),
        ];

        fn check_covered(p: &CharPartition, test: &CharSet, i: usize) -> bool {
            i < p.len() && p.start(i) <= test.start && test.end <= p.end(i)
        }

        fn check_disjoint(p: &[CharSet], test: &CharSet) -> bool {
            p.iter()
                .all(|set| test.end < set.start || set.end < test.start)
        }

        fn check_overlap(p: &[CharSet], test: &CharSet) -> bool {
            p.iter().any(|set| {
                (test.start < set.start && set.start <= test.end)
                    || (test.start <= set.end && set.end < test.end)
            })
        }

        for p in &v {
            println!("Partition: {p}");
            for set in &i {
                let c = p.interval_cover(set);
                println!("Cover for {set} = {c}");

                match c {
                    CoverResult::CoveredBy(i) => {
                        assert!(check_covered(p, set, i))
                    }
                    CoverResult::DisjointFromAll => {
                        assert!(check_disjoint(&p.list, set))
                    }
                    CoverResult::Overlaps => {
                        assert!(check_overlap(&p.list, set))
                    }
                }
            }
            println!();
        }
    }
}
