// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Partitions of an integer set
//!
//! We consider a set of N integers [0 ... n-1].
//! A partition is a division of set into K blocks for some K>=1.
//!

use std::fmt::Display;

// Implementation:
// - each block is identified by an integer between 0 and K (the block id)
// - each block is also a slice in a segments array
// - segments[0 ... n-1]: is a permutation of the n integers
// - block[j] is a pair (start, end) such that 0 <= start < end <= n:
// This means that block[j] is the set of integers in segment[start .. end].
//
// Block 0 is special: it is the empty block.
// All other blocks are non-empty.
//

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BlockHeader {
    start: usize,
    end: usize,
}

///
/// A partition divides a set of integers [0 ... N-1]
/// into disjoint, non-empty blocks.
///
#[derive(Debug, Clone)]
pub struct BasePartition {
    // number of elements
    size: usize,
    // block descriptors
    block: Vec<BlockHeader>,
    // segment = concatenation of the blocks
    segment: Box<[u32]>,
}

///
/// A full partition is a partition that also maintains a
/// mapping of element to block id: given an x, we can get
/// the block that contains x.
///
#[derive(Debug, Clone)]
pub struct Partition {
    base: BasePartition,
    // mapping from element to block id
    block_id: Box<[u32]>,
}

#[allow(dead_code)]
impl BasePartition {
    ///
    /// Create a new partition for n elements
    /// - if n == 0, the partition will contain just the empty block
    /// - if n > 0, the partition is initialized with two blocks:
    ///   the empty block (id = 0)
    ///   and block 1 that contains all elements [0 .. n-1]
    ///
    pub fn new(n: u32) -> Self {
        let size = n as usize;
        let mut segment = vec![0; size].into_boxed_slice();
        for i in 0..size {
            segment[i] = i as u32;
        }
        // one header for the empty block + one header for block 1 if n > 0
        let block = if n == 0 {
            vec![BlockHeader { start: 0, end: 0 }]
        } else {
            vec![
                BlockHeader { start: 0, end: 0 },
                BlockHeader {
                    start: 0,
                    end: size,
                },
            ]
        };
        BasePartition {
            size,
            block,
            segment,
        }
    }

    ///
    /// Number of blocks
    ///
    pub fn num_blocks(&self) -> u32 {
        self.block.len() as u32
    }

    ///
    /// Index = number of equivalence classes = number of non-empty blocks
    ///
    pub fn index(&self) -> u32 {
        self.num_blocks() - 1
    }

    ///
    /// Size of the set
    ///
    pub fn size(&self) -> u32 {
        self.size as u32
    }

    ///
    /// Size of block i
    ///
    pub fn block_size(&self, i: u32) -> u32 {
        let BlockHeader { start, end } = self.block[i as usize];
        (end - start) as u32
    }

    ///
    /// Check whether block i is smaller than block j (or has the same size)
    ///
    pub fn smaller_block(&self, i: u32, j: u32) -> bool {
        self.block_size(i) <= self.block_size(j)
    }

    ///
    /// Sort elements in block i
    ///
    pub fn sort_block(&mut self, i: u32) {
        self.slice_mut(i).sort_unstable()
    }

    ///
    /// Iterator to get all elements of block i
    ///
    pub fn block_elements(&self, i: u32) -> impl Iterator<Item = u32> + '_ {
        self.slice(i).iter().copied()
    }

    ///
    /// Pick the first element of block i
    ///
    pub fn pick_element(&self, i: u32) -> u32 {
        assert!(i > 0);
        let start = self.block[i as usize].start;
        self.segment[start]
    }

    ///
    /// Slice of self.segment corresponding to block i
    ///
    fn slice(&self, i: u32) -> &[u32] {
        let BlockHeader { start, end } = self.block[i as usize];
        &self.segment[start..end]
    }

    fn slice_mut(&mut self, i: u32) -> &mut [u32] {
        let BlockHeader { start, end } = self.block[i as usize];
        &mut self.segment[start..end]
    }

    ///
    /// Add a new block and return its id
    /// - start and end are the block limits: start is included, end is excluded.
    ///
    fn add_block(&mut self, start: usize, end: usize) -> u32 {
        debug_assert!(start < end && end <= self.size);
        let id = self.num_blocks();
        self.block.push(BlockHeader { start, end });
        id
    }

    ///
    /// Split block i at position n
    /// - assume block i is [start, end)
    /// - then block i is reduced to [start, start + n)
    ///   and a new block is created for the segment [start + n, end)
    /// - return the id of the new block
    ///
    fn split_block(&mut self, i: u32, n: usize) -> u32 {
        let i = i as usize;
        let split_point = self.block[i].start + n;
        let end_point = self.block[i].end;
        debug_assert!(split_point <= end_point);
        self.block[i].end = split_point;
        self.add_block(split_point, end_point)
    }

    ///
    /// Refine a block according to a predicate p
    /// - split block i into to sub-blocks B1 and B2
    ///   B1 = { x in block i | p(x) }
    ///   B2 = { x in block i | not p(x) }
    /// - if B1 or B2 is empty, block i is unchanged
    /// - otherwise split block i:
    ///   - elements of block i that satisfy p remain in the block
    ///     (i.e., block i is now equal to B1)
    ///   - elements of block i that do not satisfy p are added to
    ///     a new block (equal to B2)
    ///
    /// Return a pair of block ids (i1, i2) where
    /// i1 = id of B1 and i2 = id of B2.
    /// - if B1 is empty, B2 is equal to block i and the result is (0, i)
    /// - if B2 is empty, B1 is equal to block i and the result is (i, 0)
    /// - otherwise, block i is shrunk (to store B1) and a new
    ///   block j is created equal to B2, and the result is (i, j)
    ///
    pub fn refine_block<P>(&mut self, i: u32, p: P) -> (u32, u32)
    where
        P: Fn(u32) -> bool,
    {
        let s = self.slice_mut(i);
        let mut j = 0;
        for k in 0..s.len() {
            if p(s[k]) {
                if j < k {
                    s.swap(k, j);
                }
                j += 1;
            }
        }
        // 0 .. j-1 -> elements that satisfy p (B1)
        // j .. s.len()-1 -> elements that don't satisfy p (B2)
        if j == 0 {
            (0, i)
        } else if j == s.len() {
            (i, 0)
        } else {
            let k = self.split_block(i, j);
            (i, k)
        }
    }
}

#[allow(dead_code)]
impl Partition {
    ///
    /// Create a new partition for n elements
    /// - if n = 0, the partition has only the empty block
    /// - otherwise, the partition has two blocks with id 0 and 1
    ///   0 --> empty block, 1 --> [0 .. n-1]
    ///
    pub fn new(n: u32) -> Self {
        let size = n as usize;
        // all elements belong to block 1
        let block_id = vec![1; size].into_boxed_slice();
        Partition {
            base: BasePartition::new(n),
            block_id,
        }
    }

    ///
    /// Number of blocks
    ///
    pub fn num_blocks(&self) -> u32 {
        self.base.num_blocks()
    }

    ///
    /// Index = number of equivalence classes = number of non-empty blocks
    ///
    pub fn index(&self) -> u32 {
        self.base.index()
    }

    ///
    /// Size of the set
    ///
    pub fn size(&self) -> u32 {
        self.base.size()
    }

    ///
    /// Size of block i
    ///
    pub fn block_size(&self, i: u32) -> u32 {
        self.base.block_size(i)
    }

    ///
    /// Check whether block i is smaller than block j (or has the same size)
    ///
    pub fn smaller_block(&self, i: u32, j: u32) -> bool {
        self.base.smaller_block(i, j)
    }

    ///
    /// Sort elements in block i
    ///
    pub fn sort_block(&mut self, i: u32) {
        self.base.sort_block(i)
    }

    ///
    /// Iterator to get all elements of block i
    ///
    pub fn block_elements(&self, i: u32) -> impl Iterator<Item = u32> + '_ {
        self.base.block_elements(i)
    }

    ///
    /// Pick an element in block i (the first element)
    /// - block i must not be empty so i must not be 0
    ///
    pub fn pick_element(&self, i: u32) -> u32 {
        self.base.pick_element(i)
    }

    ///
    /// Block id for element x
    ///
    pub fn block_id(&self, x: u32) -> u32 {
        self.block_id[x as usize]
    }

    ///
    /// Refine a block according to a predicate p
    /// - split block i into to sub-blocks B1 and B2
    ///   B1 = { x in block i | p(x) }
    ///   B2 = { x in block i | not p(x) }
    /// - if B1 or B2 is empty, nothing changes
    /// - otherwise split block i:
    ///   - elements of block i that satisfy p remain in the block
    ///     (i.e., block i is now equal to B1)
    ///   - elements of block i that do not satisfy p are added to
    ///     a new block (equal to B2)
    ///
    /// Return a pair of block ids for (B1, B2). See [BasePartition::refine_block].
    ///
    pub fn refine_block<P>(&mut self, i: u32, p: P) -> (u32, u32)
    where
        P: Fn(u32) -> bool,
    {
        let result = self.base.refine_block(i, p);
        let (b1, b2) = result;
        if b1 != 0 && b2 != 0 {
            // b2 is the new block
            for x in self.base.block_elements(b2) {
                self.block_id[x as usize] = b2;
            }
        }
        result
    }

    ///
    /// Refine a block according to a function f and another block B
    /// - f must be defined on the partition elements (i.e., if the partition
    ///   has size N, f must be a map from [0 .. N-1] to [0 .. N-1]).
    /// - split block i into two sub-blocks B1 and B2
    ///   B1 = { y in block i | f(y) in b }
    ///   B2 = { y in block i | f(y) not in b }
    /// - the result is as in [refine_block](Self::refine_block)
    ///
    /// Warning: if i == b, this may modify block B.
    ///
    pub fn refine_block_with_fun<F>(&mut self, i: u32, f: F, b: u32) -> (u32, u32)
    where
        F: Fn(u32) -> u32,
    {
        let base = &mut self.base;
        let block_ids = &self.block_id;
        let result = base.refine_block(i, |y| block_ids[f(y) as usize] == b);
        let (b1, b2) = result;
        if b1 != 0 && b2 != 0 {
            for x in self.base.block_elements(b2) {
                self.block_id[x as usize] = b2;
            }
        }
        result
    }
}

impl Display for BasePartition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 1..self.num_blocks() {
            write!(f, "block[{i}]: ")?;
            for x in self.block_elements(i) {
                write!(f, " {x}")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl Display for Partition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.base.fmt(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
        let mut p = Partition::new(20);
        println!("Initial partition:\n{p}");

        assert_eq!(p.num_blocks(), 2);
        for i in 0..20 {
            assert_eq!(p.block_id(i), 1);
        }

        let split0 = p.refine_block(0, |x| (x & 1) == 0);
        assert_eq!(split0, (0, 0));

        let split1 = p.refine_block(1, |x| (x & 1) == 0);
        assert_eq!(split1, (1, 2));

        println!("Even/odd numbers:\n{p}");

        for i in 1..p.num_blocks() {
            p.refine_block(i, |x| x % 3 == 0);
        }
        assert_eq!(p.num_blocks(), 5);

        for i in 0..p.num_blocks() {
            p.sort_block(i);
        }
        println!("Even/odd/multiples of three:\n{p}");

        // block 0: empty
        // block 1: multiples of 6 (x % 6 == 0)
        // block 2: multiples of 3 but not of 2 (x % 6 == 3)
        // block 3: even numbers that are not multiple of 3 (x % 6 == 2 or x % 6 == 4)
        // block 4: odd numbers that are not multiple of 3  (x % 6 == 1 or x % 6 == 5)
        for i in 0..20 {
            let b = p.block_id(i);
            let expected = match i % 6 {
                0 => 1,
                1 | 5 => 4,
                2 | 4 => 3,
                3 => 2,
                _ => panic!(),
            };
            assert_eq!(b, expected)
        }

        // One more round: only block 4 should be split
        for i in 0..p.num_blocks() {
            let (b1, b2) = p.refine_block(i, |x| x % 6 == 1);
            assert_eq!(b1 != 0 && b2 != 0, i == 4);
        }

        println!("Split in 5 classes\n{p}");

        // block 4: x such that x % 6 == 1
        // new block 5: x % 6 == 5
        for i in 0..20 {
            let b = p.block_id(i);
            let expected = match i % 6 {
                0 => 1,
                1 => 4,
                2 | 4 => 3,
                3 => 2,
                5 => 5,
                _ => panic!(),
            };
            assert_eq!(b, expected);
        }
    }
}
