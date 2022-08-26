// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! A compact representation of an automaton transition table.
//! - this assumes that most states have a sparse successor function:
//!   delta(s, c) = default successor for most characters c
//!   with a small number of exceptions c1 ... ck
//! - we assume characters and states are represented by u32 integers
//!   the set of states is an interval [0 .. num_states-1]
//!   the alphabet is an interval [0 .. alphabet_size-1]
//!

use std::fmt::Display;

/// Compact table:
/// - four internal arrays to define a function f: state x alphabet -> state
/// - tables default and base are indexed from 0 to num_state-1
/// - value and check are larger tables of the same size
/// - default\[s\] = default successor for state s (set to num_states if not defined)
/// - base\[s\] = an index in table value and check
///
/// The function f is computed as follows:
///   f(s, c):
///     let k = base\[s\] + c;
///     if check\[k\] == s then value\[k\] else default\[s\]
///
#[derive(Debug)]
pub struct CompactTable {
    num_states: u32,
    alphabet_size: u32,
    default: Box<[u32]>,
    base: Box<[u32]>,
    value: Box<[u32]>,
    check: Box<[u32]>,
}

impl CompactTable {
    /// Evaluate the function at state s for character c
    pub fn eval(&self, s: u32, c: u32) -> u32 {
        let k = self.base[s as usize] as usize + c as usize;
        if self.check[k] == s {
            self.value[k]
        } else {
            self.default[s as usize]
        }
    }

    /// Size = size of the value and check arrays
    pub fn size(&self) -> usize {
        self.value.len()
    }

    /// Number of states in the domain
    pub fn num_states(&self) -> usize {
        self.num_states as usize
    }

    /// Alphabet size
    pub fn alphabet_size(&self) -> usize {
        self.alphabet_size as usize
    }
}

impl Display for CompactTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let num_states = self.num_states();
        writeln!(f, "Map")?;
        for i in 0..self.size() {
            let c = self.check[i];
            if c != num_states as u32 {
                let b = self.base[c as usize];
                writeln!(f, "  {}, {} -> {}", c, i - b as usize, self.value[i])?;
            }
        }
        writeln!(f, "Default")?;
        for i in 0..num_states {
            writeln!(f, "  {} -> {}", i, self.default[i])?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct CompactTableBuilder {
    num_states: u32,
    alphabet_size: u32,
    default: Box<[u32]>,
    base: Box<[u32]>,
    value: Vec<u32>,
    check: Vec<u32>,
}

impl CompactTableBuilder {
    ///
    /// Get a new builder
    /// both num_states and alphabet_size must be positive
    ///
    pub fn new(num_states: u32, alphabet_size: u32) -> Self {
        assert!(num_states > 0 && alphabet_size > 0);

        let n = num_states as usize;
        let default = vec![0; n].into_boxed_slice();
        let base = vec![0; n].into_boxed_slice();

        let m = alphabet_size as usize;
        let value = vec![0; m];
        let check = vec![num_states; m];

        CompactTableBuilder {
            num_states,
            alphabet_size,
            default,
            base,
            value,
            check,
        }
    }

    ///
    /// Set the default value for state i
    ///
    pub fn set_default(&mut self, i: u32, def: u32) {
        debug_assert!(def < self.num_states);
        self.default[i as usize] = def;
    }

    ///
    /// Extend vectors value and check to the new_size
    ///
    fn resize(&mut self, new_size: usize) {
        self.check.resize(new_size, self.num_states);
        self.value.resize(new_size, 0);
    }

    ///
    /// Check whether setting base\[i\] to b conflicts
    /// with a successor array.
    ///
    fn base_conflicts(&self, b: u32, successors: &[(u32, u32)]) -> bool {
        let b = b as usize;
        successors
            .iter()
            .any(|(c, _)| self.check[b + *c as usize] != self.num_states)
    }

    ///
    /// Store the successors of i at base b
    ///
    fn store_successors(&mut self, i: u32, b: u32, successors: &[(u32, u32)]) {
        self.base[i as usize] = b;
        for (c, v) in successors {
            let k = b as usize + *c as usize;
            self.check[k] = i;
            self.value[k] = *v;
        }
    }

    /// Store the successor map for state i
    /// the successor map is a list of pairs (char, successor state)
    pub fn set_successors(&mut self, i: u32, successors: &[(u32, u32)]) {
        let mut b = 0;
        while self.base_conflicts(b, successors) {
            b += 1;
            if b as usize + self.alphabet_size as usize > self.value.len() {
                let new_size = 2 * self.value.len();
                assert!(new_size >= b as usize + self.alphabet_size as usize);
                self.resize(new_size);
            }
        }
        self.store_successors(i, b, successors);
    }

    /// Build the map
    pub fn build(&mut self) -> CompactTable {
        let &max_base = self.base.iter().max().unwrap();
        let max_index = max_base as usize + self.alphabet_size as usize;
        self.value.truncate(max_index);
        self.check.truncate(max_index);

        let default = std::mem::take(&mut self.default);
        let base = std::mem::take(&mut self.base);
        let value = std::mem::take(&mut self.value).into_boxed_slice();
        let check = std::mem::take(&mut self.check).into_boxed_slice();

        CompactTable {
            num_states: self.num_states,
            alphabet_size: self.alphabet_size,
            default,
            base,
            value,
            check,
        }
    }
}
