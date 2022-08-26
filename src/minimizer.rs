// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Minimization of deterministic finite-state automata
//!

use std::fmt::Display;

use crate::{
    fast_sets::FastSet,
    partitions::{BasePartition, Partition},
};

//
// The automaton is defined by
// - a finite set of state S
// - an alphabet A
// - a transition function delta: S x A -> S
// - a set of final states F
//
// Minimization
// ------------
// - maintain a partition of S into disjoint blocks
// - initially, there are two blocks: F and S-F
// - refine the partition until it satisfies the following condition:
//     for any pair of blocks (B, D) and any letter c in the alphabet,
//     either delta(D, c) is included in B
//     or delta(D, c) and B are disjoint
//   where delta(D, c) is { delta(s, c) | s in D }.
// - if the condition doesn't hold: there are B, c, and D
//   such that
//      delta(D, c) intersect B
//      delta(D, c) is not included in B
//   then refine the partition by splitting D into two sub-blocks:
//       D1 = { s in D | delta(s, c) is in B }
//       D2 = { s in D | delta(s, c) is not in B }
//
// Hopcroft's algorithm
// --------------------
// Maintain a set of pairs (B, c) called splitters.
// - the initial splitter set either contains all pairs (F, c) for c in the
//   alphabet or all pairs (S - F, c) for c in the alphabet.
//
// Refinement step:
// - pick a splitter (B, c)
// - let pred(B, c) = { s in S | delta(s, c) is in B } (predecessors of B via c)
// - collect all the blocks D such that D and pred(B, c) intersect.
// - for each such block D: compute
//      D1 = { s in D | delta(s, c) in B }
//      D2 = { s in D | delta(s, c) not in B}
// - D1 is non-empty by construction.
// - if D2 is non-empty, then
//   1) refine the partition: replace D with D1 and D2.
//   2) update the splitter set as follows:
//      for every character a in A:
//      - if (D, a) is in the splitter set, then replace it with (D1, a) and (D2, a)
//      - if (D, a) is not in the splitter set, then let D' be the smallest of D1 and D2;
//        add (D', a) to the splitter set.
//
// Do this until the set of splitters is empty.
//
// Data structures
// ----------------
// - first, we assume the set of states is [0 .. N-1] and the alphabet is [0 .. M-1]
//   for some fixed integers N>0 and M>0.
// - main_partition is a partition of [0 .. N-1]
// - for every c in [0 .. M-1], we also keep pred_classes(c) = a partition of [0 .. N-1].
//   Each block in pred_classes(c) is pred(B, c) for some block B in the main partition.
// - for every block B in the main_partition, we keep the list of all splitters (B, c, cid)
//   where c is a character, cid is the id of the block of pred_classes(c) equal to pred(B, c),
//   and cid is not empty.
// - each splitter structure also includes a Boolean flag active
// - the splitter set is the set of all active splitters
//

#[derive(Debug, Clone, PartialEq, Eq)]
struct Splitter {
    block: u32, // block id for B in the main partition,
    char: u32,  // character c
    class: u32, // block id for pred(B, c) in pred_classes(c)
    active: bool,
}

impl Display for Splitter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Splitter({}, {}, {}, {})",
            self.block, self.char, self.class, self.active
        )
    }
}

#[derive(Debug, Clone)]
struct SplitterItem {
    char: u32,
    class: u32,
    active: bool,
}

impl SplitterItem {
    fn to_splitter(&self, block: u32) -> Splitter {
        Splitter {
            block,
            char: self.char,
            class: self.class,
            active: self.active,
        }
    }

    fn from_splitter(s: &Splitter) -> SplitterItem {
        SplitterItem {
            char: s.char,
            class: s.class,
            active: s.active,
        }
    }
}

#[derive(Debug, Clone)]
struct CharClassPair {
    char: u32,
    class: u32,
}

///
/// List of pairs char/class attached to a block
/// - the list is divided into two parts
/// - pairs for active splitters come first at index [0 .. num_active-1]
/// - pairs for inactive splitters are in list[num_active .. ]
///
#[derive(Debug, Clone, Default)]
struct SplitterList {
    num_active: usize,
    list: Vec<CharClassPair>,
}

///
/// Iterator to enumerate the elements of a list
/// - for each pair (char, class), the iterator returns a triple (char, class, active)
///
struct SplitterListIterator<'a> {
    list: &'a SplitterList,
    index: usize,
}

impl SplitterList {
    fn add(&mut self, s: SplitterItem) {
        let list = &mut self.list;
        let i = list.len();
        list.push(CharClassPair {
            char: s.char,
            class: s.class,
        });
        if s.active {
            if self.num_active < i {
                list.swap(self.num_active, i);
            }
            self.num_active += 1;
        }
    }

    fn pick_active(&mut self) -> &CharClassPair {
        debug_assert!(self.num_active > 0);
        let list = &self.list;
        self.num_active -= 1;
        &list[self.num_active]
    }

    fn has_active_items(&self) -> bool {
        self.num_active > 0
    }

    fn iter(&self) -> SplitterListIterator<'_> {
        SplitterListIterator {
            list: self,
            index: 0,
        }
    }
}

impl<'a> Iterator for SplitterListIterator<'a> {
    type Item = SplitterItem;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.index;
        let list = &self.list.list;
        if i < list.len() {
            self.index += 1;
            let active = i < self.list.num_active;
            let pair = &list[i];
            Some(SplitterItem {
                char: pair.char,
                class: pair.class,
                active,
            })
        } else {
            None
        }
    }
}

// For every block b: list[b] = list of splitters for b
// active_block = index of the last block for which we picked a splitter
#[derive(Debug, Clone)]
struct SplitterSet {
    list: Vec<SplitterList>,
    active_block: usize,
}

impl SplitterSet {
    fn new() -> SplitterSet {
        let list = Vec::with_capacity(8);
        SplitterSet {
            list,
            active_block: 0,
        }
    }

    fn take_list(&mut self, b: u32) -> SplitterList {
        std::mem::take(&mut self.list[b as usize])
    }

    fn add_splitter(&mut self, s: &Splitter) {
        let b = s.block as usize;
        if self.list.len() <= b {
            self.list.resize_with(b + 1, Default::default);
        }
        self.list[b].add(SplitterItem::from_splitter(s))
    }

    // Check whether one list[b] has an active item.
    // If so, store b in self->active_block and return true.
    // If not return false.
    fn has_active_splitter(&mut self) -> bool {
        let l = &self.list;
        let b = self.active_block;
        if l[b].has_active_items() {
            true
        } else {
            for (b, list) in l.iter().enumerate() {
                if list.has_active_items() {
                    self.active_block = b;
                    return true;
                }
            }
            false
        }
    }

    fn pick_splitter(&mut self) -> Option<Splitter> {
        if self.has_active_splitter() {
            let b = self.active_block;
            let l = &mut self.list[b];
            let pair = l.pick_active();
            Some(Splitter {
                block: b as u32,
                char: pair.char,
                class: pair.class,
                active: false,
            })
        } else {
            None
        }
    }

    fn iter(&self) -> impl Iterator<Item = &SplitterList> {
        self.list.iter()
    }
}

#[derive(Debug, Clone)]
pub struct Minimizer<D, F> {
    // Automaton specification
    num_states: u32,
    alphabet_size: u32,
    delta: D,
    is_final: F,
    // Partitions
    main_partition: Partition,
    pred_classes: Box<[BasePartition]>,
    // Splitters
    splitters: SplitterSet,
}

impl<D, F> Display for Minimizer<D, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "Minimizer: {} states, {} chars",
            self.num_states, self.alphabet_size
        )?;
        writeln!(f, "main partition")?;
        writeln!(f, "{}", self.main_partition)?;
        for (i, p) in self.pred_classes.iter().enumerate() {
            writeln!(f, "pred_class[{}]", i)?;
            writeln!(f, "{}", p)?;
        }
        writeln!(f, "Active splitters")?;
        for (i, l) in self.splitters.iter().enumerate() {
            for s in l.iter() {
                if s.active {
                    writeln!(f, "  {}", s.to_splitter(i as u32))?;
                }
            }
        }
        writeln!(f, "Inactive splitters")?;
        for (i, l) in self.splitters.iter().enumerate() {
            for s in l.iter() {
                if !s.active {
                    writeln!(f, "  {}", s.to_splitter(i as u32))?;
                }
            }
        }
        Ok(())
    }
}

impl<D, F> Minimizer<D, F>
where
    D: Fn(u32, u32) -> u32,
    F: Fn(u32) -> bool,
{
    //
    // Update the splitter lists after a block was split
    // - the refinement splits block i into (i, j)
    // - some states that were in block i have moved to a new block j
    //   some states that were in block i stayed there
    //
    fn upate_splitters_after_refinement(&mut self, i: u32, j: u32) {
        let main = &self.main_partition;
        let delta = &self.delta;

        let old_splitters = self.splitters.take_list(i);
        for s in old_splitters.iter() {
            // s is (i, c, class)
            // { x | delta(x, c) is in block i } is not empty
            debug_assert!(s.class != 0);
            let c = s.char;

            // refine class in pred_classes[c]
            let p = &mut self.pred_classes[c as usize];
            let (class1, class2) = p.refine_block(s.class, |x| main.block_id(delta(x, c)) == i);

            // we create two new splitters
            // both of them are active if s is active
            // only one of them is active if s is inactive
            let active1;
            let active2;
            if s.active {
                active1 = true;
                active2 = true;
            } else if p.smaller_block(class1, class2) {
                active1 = true;
                active2 = false;
            } else {
                active1 = false;
                active2 = true;
            }

            if class1 != 0 {
                self.splitters.add_splitter(&Splitter {
                    block: i,
                    char: c,
                    class: class1,
                    active: active1,
                });
            }

            if class2 != 0 {
                self.splitters.add_splitter(&Splitter {
                    block: j,
                    char: c,
                    class: class2,
                    active: active2,
                });
            }
        }
    }

    //
    // split the main partition into final and non-final states
    // initialize the splitters with the smallest of the two blocks
    //
    fn init_main_partition(&mut self) {
        let main_partition = &mut self.main_partition;
        debug_assert_eq!(main_partition.num_blocks(), 2);

        //
        // Refine the main partition into final and non-final states
        // If the result is not a split, there's nothing to do: either all
        // states are final or no state is final.
        //
        let (i, j) = main_partition.refine_block(1, &self.is_final);
        if i != 0 && j != 0 {
            debug_assert!(i == 1 && j == 2);
            // i = block of final states
            // j = block of non-final states
            // both blocks are non-empty.
            self.upate_splitters_after_refinement(i, j);
        }
    }

    //
    // Collect all blocks that could be refined by a splitter
    // - store their ids in set
    // - block b is included if it is not a singleton and if it contains a
    //   state x of pred(B, c) where B = s.block and c = s.char.
    //
    fn collect_refinement_candidates(&self, s: &Splitter, set: &mut FastSet) {
        set.reset();
        let p = &self.pred_classes[s.char as usize];
        // p.block_elements(s.class) is pred(B, c)
        for x in p.block_elements(s.class) {
            let b = self.main_partition.block_id(x);
            if self.main_partition.block_size(b) > 1 {
                set.insert(b)
            }
        }
    }

    //
    // Check whether block b is refined by splitter s.
    // If so, update the main partition and the splitter list.
    //
    // Block b must be a refinement candidate for s (i.e., b intersects
    // with pred(s.block, s.char)).
    //
    // Warning: if b == s.block, then s.block will be modified.
    // So refining s.block with s must be done last, after all blocks
    // other than s.block have been refined by s.
    //
    fn refine_block_with_splitter(&mut self, s: &Splitter, b: u32) {
        let main = &mut self.main_partition;
        let delta = &self.delta;

        // Split B into B1 and B2
        //  B1 = { x in B | delta(x, s) is in B }
        //  B2 = { x in B | delta(s, x) is not in B }
        // By assumption B1 is not empty.
        let (i, j) = main.refine_block_with_fun(b, |x| delta(x, s.char), s.block);
        debug_assert!(i != 0); // B1 is not empty
        if j != 0 {
            // if j == 0, B2 is empty so nothing changes
            debug_assert_eq!(i, b);
            self.upate_splitters_after_refinement(i, j)
        }
    }

    //
    // Refine the main partition using splitter s
    //
    fn refine_with_splitter(&mut self, s: &Splitter) {
        let set = &mut FastSet::new(self.main_partition.num_blocks());
        self.collect_refinement_candidates(s, set);
        let self_refine = set.contains(s.block);
        if self_refine {
            set.remove(s.block);
        }
        for b in set.iter() {
            self.refine_block_with_splitter(s, b)
        }
        if self_refine {
            // must be done last
            self.refine_block_with_splitter(s, s.block)
        }
    }

    //
    // Pick an active splitter and mark it as inactive
    // - return None if all splitters are inactive
    fn pick_splitter(&mut self) -> Option<Splitter> {
        self.splitters.pick_splitter()
    }

    #[allow(dead_code)]
    fn print_splitters(&self) {
        println!("Splitters");
        for (i, l) in self.splitters.iter().enumerate() {
            for s in l.iter() {
                print!(
                    "  {}: pred({}, {}) = {{",
                    s.to_splitter(i as u32),
                    i,
                    s.char
                );
                for x in self.pred_classes[s.char as usize].block_elements(s.class) {
                    print!(" {}", x);
                }
                println!(" }}");
            }
        }
        println!();
    }

    //
    // Refine the partition until fix point with trace of each step
    //
    #[allow(dead_code)]
    pub fn refine_and_trace(&mut self) {
        let mut round = 0;

        println!("Initial partition");
        println!("{}", self.main_partition);
        // self.print_splitters();

        while self.main_partition.index() < self.num_states {
            round += 1;
            match self.pick_splitter() {
                Some(s) => {
                    println!("--- round {} ---", round);
                    println!("{}", s);
                    print!("pre({}, {}) = {{", s.block, s.char);
                    for x in self.pred_classes[s.char as usize].block_elements(s.class) {
                        print!(" {}", x);
                    }
                    println!(" }}");
                    self.refine_with_splitter(&s);
                    println!("After refinement");
                    println!("{}", self.main_partition);
                    // self.print_splitters();
                }
                None => break,
            }
        }
    }

    ///
    /// Refine the state partition until fix point
    /// - return the result (i.e., equivalence relation on states)
    ///
    pub fn refine(&mut self) -> &Partition {
        while self.main_partition.index() < self.num_states {
            match self.pick_splitter() {
                Some(s) => self.refine_with_splitter(&s),
                None => break,
            }
        }
        &self.main_partition
    }

    pub fn new(num_states: u32, alphabet_size: u32, delta: D, is_final: F) -> Self {
        let main_partition = Partition::new(num_states);
        let alpha_size = alphabet_size as usize;
        let mut classes = Vec::with_capacity(alpha_size);
        for _ in 0..alpha_size {
            classes.push(BasePartition::new(num_states));
        }
        let mut splitters = SplitterSet::new();
        for c in 0..alphabet_size {
            splitters.add_splitter(&Splitter {
                block: 1,
                char: c,
                class: 1,
                active: false,
            });
        }
        let mut m = Minimizer {
            num_states,
            alphabet_size,
            delta,
            is_final,
            main_partition,
            pred_classes: classes.into_boxed_slice(),
            splitters,
        };
        m.init_main_partition();
        m
    }
}
