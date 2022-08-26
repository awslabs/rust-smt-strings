// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! FastSets: sets of integers in an interval [0..N]
//!

use std::fmt::Display;

///
/// A set of integers in an interval [0 .. N-1]
/// - elements are u32 integers
/// - the bound N is specified when the set is created
/// - addition/removal/reset are O(1) operations
///
// Invariants:
// - elem[0 .. size-1] lists the elements (no special order)
// - for every x in [0 .. N-1], pos[x] is an index in elem
// - x is in the set iff pos[x] < size and elem[pos[x]] == x
//
#[derive(Debug)]
pub struct FastSet {
    max: u32,
    size: u32,
    pos: Box<[u32]>,
    elem: Box<[u32]>,
}

///
/// Iterator to get all the elements of a fast set
///
#[derive(Debug)]
pub struct FastSetIterator<'a> {
    elem: &'a [u32],
    index: usize,
    size: usize,
}

impl Display for FastSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for i in 0..self.size {
            write!(f, " {}", self.elem[i as usize])?;
        }
        write!(f, " }}")
    }
}

#[allow(dead_code)]
impl FastSet {
    ///
    /// Create an empty set for integers in the range 0 .. max
    ///
    pub fn new(max: u32) -> Self {
        let n = max as usize;
        let pos = vec![0; n].into_boxed_slice();
        let elem = vec![0; n].into_boxed_slice();
        FastSet {
            max,
            size: 0,
            pos,
            elem,
        }
    }

    ///
    /// Set cardinality
    ///
    pub fn card(&self) -> u32 {
        self.size
    }

    ///
    /// Check whether element x is in the set
    /// - x must be between 0 and max-1
    ///
    pub fn contains(&self, x: u32) -> bool {
        debug_assert!(x < self.max);
        let i = self.pos[x as usize];
        i < self.size && self.elem[i as usize] == x
    }

    ///
    /// Add element x to the set
    ///
    pub fn insert(&mut self, x: u32) {
        debug_assert!(x < self.max);
        let i = self.pos[x as usize];
        let s = self.size;
        if i >= s || self.elem[i as usize] != x {
            // x is not in the set
            self.pos[x as usize] = s;
            self.elem[s as usize] = x;
            self.size += 1;
        }
    }

    ///
    /// Remove element x from the set
    ///
    pub fn remove(&mut self, x: u32) {
        debug_assert!(x < self.max);
        let i = self.pos[x as usize];
        let mut s = self.size;
        if i < s && self.elem[i as usize] == x {
            // x is in the set as index i
            s -= 1;
            let y = self.elem[s as usize];
            self.pos[y as usize] = i;
            self.elem[i as usize] = y;
            self.size = s;
        }
    }

    ///
    /// Empty the set
    ///
    pub fn reset(&mut self) {
        self.size = 0;
    }

    ///
    /// Iterator
    ///
    pub fn iter(&self) -> FastSetIterator<'_> {
        FastSetIterator {
            elem: &self.elem,
            index: 0,
            size: self.size as usize,
        }
    }
}

impl<'a> Iterator for FastSetIterator<'a> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.index;
        if i < self.size {
            self.index += 1;
            Some(self.elem[i])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
        let set = &mut FastSet::new(100);
        set.insert(10);
        set.insert(20);
        set.insert(10);
        set.insert(40);
        set.insert(40);

        println!("After adding 10, 20, 40: {}", set);
        assert!(set.contains(10));
        assert!(set.contains(20));
        assert!(set.contains(40));
        assert!(!set.contains(30));
        assert_eq!(set.card(), 3);

        for x in set.iter() {
            println!("Element: {}", x);
            assert!(set.contains(x));
        }

        set.remove(30);
        set.remove(40);
        println!("After removing 30, 40: {}", set);
        assert!(set.contains(10));
        assert!(set.contains(20));
        assert!(!set.contains(30));
        assert!(!set.contains(40));
        assert_eq!(set.card(), 2);

        set.remove(10);
        println!("After removing 10: {}", set);
        assert!(set.contains(20));
        assert!(!set.contains(10));
        assert!(!set.contains(30));
        assert!(!set.contains(40));
        assert_eq!(set.card(), 1);

        set.reset();
        println!("After reset: {}", set);
        assert!(!set.contains(20));
        assert!(!set.contains(10));
        assert!(!set.contains(30));
        assert!(!set.contains(40));
        assert_eq!(set.card(), 0);
    }
}
