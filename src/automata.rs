// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Deterministic finite-state automata
//!
//! States are indexed by an integer from 0 to N-1 where N is the number of states.
//!
//! The alphabet is divided in equivalence classes such that all characters in an equivalence
//! class have the same transitions.
//!
//! More precisely, a character partition is attached to every state of an automaton.
//! The partition consists of disjoint character intervals (see [character_sets](crate::character_sets)).
//! If the i-th interval in the partition of state `s` is interval [a<sub>i</sub>, b<sub>i</sub>] then all
//! character in this interval have the same successors `delta(s, i)`.
//! In addition, state `s` may have a default successor, that is, the successor state of `s` for characters
//! that do not belong to any interval [a<sub>i</sub>, b<sub>i</sub>].
//!
//! Function [combined_char_partition](Automaton::combined_char_partition) constructs a
//! partition of the alphabet that is valid for all states of an automaton. If
//! two characters `c1` and `c2` are in the same class in the combined partition, then we
//! have `delta(s, c1) = delta(s, c2)` for any state `s` of the automaton.
//!
//! Function [pick_alphabet](Automaton::pick_alphabet) returns a vector of representative
//! characters (i.e., one element in each class of the combined partition).
//!
use std::{collections::HashMap, fmt::Display, hash::Hash};

use crate::{
    bfs_queues::BfsQueue,
    character_sets::*,
    compact_tables::{CompactTable, CompactTableBuilder},
    errors::*,
    minimizer::Minimizer,
    partitions::Partition,
    smt_strings::SmtString,
};

///
/// Deterministic finite state automaton
///
#[derive(Debug)]
pub struct Automaton {
    // number of states
    num_states: usize,
    // number of final states
    num_final_states: usize,
    // index of the initial state
    initial_state: usize,
    // array of states
    states: Box<[State]>,
}

///
/// State of an automaton
///
#[derive(Debug)]
pub struct State {
    // id of a state (an index between 0 and num_states)
    id: usize,
    // whether this state is final
    is_final: bool,
    // character classes for which successors are defined
    classes: CharPartition,
    // successor[i] = index of the successor state for the i-th interval in the class partition
    // so the successor array has as many elements as classes has intervals.
    successor: Box<[usize]>,
    // default successor for character outside any of the class partition intervals
    default_successor: Option<usize>,
}

///
/// Iterator to list the transitions from a state
/// - successors are given as pairs (class id, reference to successor state)
///
#[derive(Debug)]
pub struct EdgeIterator<'a> {
    state_array: &'a [State],
    state: &'a State,
    index: usize,
}

///
/// Iterator to enumerate the final states of an automaton
///
#[derive(Debug)]
pub struct FinalStateIterator<'a> {
    state_array: &'a [State],
    index: usize,
}

//
// Remap structure for automata minimization
// 1) assume equivalent nodes are mapped to a new id
// 2) for every equivalence class, one node is taken as representative
// The mapping stores this in two arrays:
// - for every old node id i: new_id[i] = new id for node
// - for every new node id j: old_id[j] = id of the old node that's representative
//   of the class of j.
//
#[derive(Debug)]
struct StateMapping {
    new_id: Vec<usize>,
    old_id: Vec<usize>,
}

impl StateMapping {
    // Build a mapping from an array of nodes to keep
    // - nodes_to_keep must not contain duplicates
    // - the mapping assigns new id k to node j such that nodes_to_keep[k] = j.
    // - num_nodes = number of old nodes
    fn from_array(num_nodes: usize, nodes_to_keep: &[usize]) -> Self {
        let mut new_id = vec![0; num_nodes];
        let num_new_nodes = nodes_to_keep.len();
        let mut old_id = vec![0; num_new_nodes];
        for (i, &node_id) in nodes_to_keep.iter().enumerate() {
            new_id[node_id] = i;
            old_id[i] = node_id;
        }
        StateMapping { new_id, old_id }
    }

    //
    // Build a mapping from a state partition
    // - pick one state to keep in each block of the partition
    // - map nodes to their block id - 1 (since block 0 is empty)
    //
    fn from_partition(p: &Partition) -> Self {
        let num_nodes = p.size() as usize;
        let mut new_id = vec![0; num_nodes];
        let num_new_nodes = p.index() as usize;
        let mut old_id = vec![0; num_new_nodes];
        for s in 0..p.size() {
            new_id[s as usize] = (p.block_id(s) - 1) as usize;
        }
        for b in 1..p.num_blocks() {
            let s = p.pick_element(b);
            old_id[b as usize - 1] = s as usize;
        }
        StateMapping { new_id, old_id }
    }

    // Number of new states
    fn num_new_states(&self) -> usize {
        self.old_id.len()
    }

    // Check whether old id is representative of its class
    fn is_class_rep(&self, id: usize) -> bool {
        self.old_id[self.new_id[id]] == id
    }
}

impl Automaton {
    /// Get the initial state
    pub fn initial_state(&self) -> &State {
        &self.states[self.initial_state]
    }

    /// Get a state from its id
    /// panics if the id is out of range
    pub fn state(&self, id: usize) -> &State {
        &self.states[id]
    }

    /// Number of states
    pub fn num_states(&self) -> usize {
        self.num_states
    }

    /// Number of final states
    pub fn num_final_states(&self) -> usize {
        self.num_final_states
    }

    /// Default successor of a state
    pub fn default_successor(&self, s: &State) -> Option<&State> {
        s.default_successor.map(|i| &self.states[i])
    }

    ///
    /// Successor for a character class
    ///
    /// The class id must be valid for state s
    ///
    /// # Panics
    ///
    /// If cid is of the form ClassId::Interval(i) but i is larger than
    /// the number of successors of s.
    ///
    /// If cid is of the form ClassId::Complement but s has no default successor.
    ///
    pub fn class_next(&self, s: &State, cid: ClassId) -> &State {
        debug_assert!(s.valid_class_id(cid));
        let i = match cid {
            ClassId::Interval(i) => s.successor[i],
            ClassId::Complement => s.default_successor.unwrap(),
        };
        &self.states[i]
    }

    ///
    /// Successor of a state via a character set
    ///
    /// # Errors
    ///
    /// If this set overlaps two or more successor classes,
    /// produce [Error::AmbiguousCharSet].
    ///
    pub fn char_set_next(&self, s: &State, set: &CharSet) -> Result<&State, Error> {
        let cid = s.classes.class_of_set(set)?;
        Ok(self.class_next(s, cid))
    }

    ///
    /// Successor of a state via a character
    ///
    pub fn next(&self, s: &State, c: u32) -> &State {
        let cid = s.classes.class_of_char(c);
        self.class_next(s, cid)
    }

    /// Successor of a state via an SMT string
    pub fn str_next<'a>(&'a self, s: &'a State, str: &SmtString) -> &'a State {
        str.iter().fold(s, |s1, c| self.next(s1, *c))
    }

    /// Check whether an SMT string is accepted
    pub fn accepts(&self, str: &SmtString) -> bool {
        self.str_next(self.initial_state(), str).is_final
    }

    /// Iterator to got through the states
    pub fn states(&self) -> impl Iterator<Item = &State> {
        self.states.iter()
    }

    /// Iterator to list the out edges of a state
    ///
    /// The iterator produces a list of pairs (ClassId, SuccessorState)
    /// for every class in the state's character partition.
    ///
    pub fn edges<'a>(&'a self, s: &'a State) -> EdgeIterator<'a> {
        EdgeIterator {
            state_array: &self.states,
            state: s,
            index: 0,
        }
    }

    /// Iterator to list the final states
    pub fn final_states(&self) -> FinalStateIterator<'_> {
        FinalStateIterator {
            state_array: &self.states,
            index: 0,
        }
    }

    ///
    /// Merge the state partitions and return the result.
    /// This returns an abstraction of the automaton's alphabet.
    ///
    /// Every class in the returned partition contains equivalent
    /// characters: if c1 and c2 are in one class, then
    /// delta(s, c1) = delta(s, c2) for every state s of the automaton.
    ///
    pub fn combined_char_partition(&self) -> CharPartition {
        merge_partition_list(self.states().map(|x| &x.classes))
    }

    /// Get a representative character from the combined partition
    pub fn pick_alphabet(&self) -> Vec<u32> {
        self.combined_char_partition().picks().collect()
    }

    ///
    /// Compile the successor function.
    ///
    /// The successor function is defined on state indices and character indices
    /// and it returns a state index. More precisely, it starts with building the
    /// representative alphabet for this automaton (see [pick_alphabet](Self::pick_alphabet)). If
    /// the automaton has N states and the representative alphabet has M characters,
    /// then the compiled successor function is defined on [0 .. N-1] x [0 .. M-1]
    /// and return an index in [0 .. N-1].
    ///
    pub fn compile_successors(&self) -> CompactTable {
        let alphabet = self.pick_alphabet();
        let num_states = self.num_states as u32;
        let alpha_size = alphabet.len() as u32;
        let mut builder = CompactTableBuilder::new(num_states, alpha_size);
        for s in self.states() {
            let id = s.id as u32;
            if s.has_default_successor() {
                let d = s.default_successor.unwrap();
                builder.set_default(id, d as u32);
            }
            let suc: Vec<(u32, u32)> = alphabet
                .iter()
                .enumerate()
                .filter(|(_, &c)| !s.char_maps_to_default(c))
                .map(|(i, &c)| (i as u32, self.next(s, c).id as u32))
                .collect();
            builder.set_successors(id, &suc);
        }
        builder.build()
    }

    /// Apply a remapping
    fn remap_nodes(&mut self, remap: &StateMapping) {
        let i = self.initial_state;
        self.initial_state = remap.new_id[i];

        self.num_final_states = 0;
        let num_new_nodes = remap.num_new_states();
        let mut new_states = Vec::with_capacity(num_new_nodes);
        for i in 0..num_new_nodes {
            let old_id = remap.old_id[i];
            let s = &mut self.states[old_id];
            new_states.push(s.remap_nodes(remap));
            debug_assert!(new_states[i].id == i);
            if s.is_final {
                debug_assert!(new_states[i].is_final);
                self.num_final_states += 1;
            }
        }

        self.num_states = num_new_nodes;
        self.states = new_states.into();
    }

    /// Remove unreachable states
    pub fn remove_unreachable_states(&mut self) {
        let mut queue = BfsQueue::new();
        let mut reachable = Vec::new();
        queue.push(self.initial_state);
        while let Some(i) = queue.pop() {
            reachable.push(i);
            let s = self.state(i);
            for (_, next) in self.edges(s) {
                queue.push(next.id);
            }
        }
        reachable.sort_unstable();
        let remap = StateMapping::from_array(self.num_states, &reachable);
        self.remap_nodes(&remap);
    }

    /// Minimize the automaton
    pub fn minimize(&mut self) {
        let is_final = |i: u32| self.state(i as usize).is_final;
        let transition_map = self.compile_successors();
        let delta = |i, j| transition_map.eval(i, j);
        let num_states = self.num_states as u32;
        let alphabet_size = transition_map.alphabet_size() as u32;
        let mut minimizer = Minimizer::new(num_states, alphabet_size, delta, is_final);
        let p = minimizer.refine();
        if (p.index() as usize) < self.num_states {
            let remap = StateMapping::from_partition(p);
            self.remap_nodes(&remap)
        }
    }

    /// test minimizer
    #[cfg(test)]
    pub fn test_minimizer(&self) {
        let is_final = |i: u32| self.state(i as usize).is_final;
        let transition_map = self.compile_successors();
        let delta = |i, j| transition_map.eval(i, j);
        let num_states = self.num_states as u32;
        let alphabet_size = transition_map.alphabet_size() as u32;
        let mut minimizer = Minimizer::new(num_states, alphabet_size, delta, is_final);
        minimizer.refine_and_trace();
    }
}

impl State {
    /// State id
    pub fn id(&self) -> usize {
        self.id
    }

    /// Check whether a state is final
    pub fn is_final(&self) -> bool {
        self.is_final
    }

    /// Number of transitions, not including the default
    pub fn num_successors(&self) -> usize {
        self.classes.len()
    }

    /// Check whether a state has a default successor
    pub fn has_default_successor(&self) -> bool {
        self.default_successor.is_some()
    }

    /// Get the default successor
    pub fn default_successor(&self) -> Option<usize> {
        self.default_successor
    }

    /// Check whether a class id is valid for this state
    /// - a class id Interval(i) is valid if i < number of transitions
    /// - class id Complement is valid if there's a default successor defined
    pub fn valid_class_id(&self, cid: ClassId) -> bool {
        self.classes.valid_class_id(cid)
    }

    /// Check whether character c maps to the default successor
    pub fn char_maps_to_default(&self, c: u32) -> bool {
        self.has_default_successor() && self.classes.class_of_char(c) == ClassId::Complement
    }

    /// Iterate through all valid class ids for this state
    pub fn char_classes(&self) -> ClassIdIterator<'_> {
        self.classes.class_ids()
    }

    /// Return the class id for a character
    pub fn class_of_char(&self, x: u32) -> ClassId {
        self.classes.class_of_char(x)
    }

    /// Pick a character in each class of this state's character partition
    pub fn char_picks(&self) -> PickIterator<'_> {
        self.classes.picks()
    }

    /// Iterate through the character ranges defined for this state.
    ///
    /// Same as [char_classes](Self::char_classes), except that the
    /// complementary class is not
    /// included.
    pub fn char_ranges(&self) -> impl Iterator<Item = &CharSet> {
        self.classes.ranges()
    }

    /// Apply remapping to a state and return the updated state
    /// - `self` must be a state to keep as defined by remap
    /// This operation is destructive:
    /// - self.classes is modified (replaced by an empty partition)
    /// - self.successors is lost too.
    fn remap_nodes(&mut self, remap: &StateMapping) -> Self {
        let old_id = self.id;
        debug_assert!(remap.is_class_rep(old_id));
        let new_id = remap.new_id[old_id];
        let new_default = self.default_successor.map(|i| remap.new_id[i]);
        // take then modify the successors array in place
        let mut new_successors = std::mem::take(&mut self.successor);
        for s in new_successors.as_mut() {
            *s = remap.new_id[*s];
        }
        let new_classes = std::mem::take(&mut self.classes);
        State {
            id: new_id,
            is_final: self.is_final,
            default_successor: new_default,
            successor: new_successors,
            classes: new_classes,
        }
    }
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "s{}", self.id)
    }
}

impl Display for Automaton {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn plural(n: usize) -> &'static str {
            if n == 1 {
                ""
            } else {
                "s"
            }
        }

        writeln!(f, "{} states", self.num_states)?;
        writeln!(f, "initial state: {}", self.initial_state())?;
        write!(f, "final state{}:", plural(self.num_final_states))?;
        for s in self.final_states() {
            write!(f, " {}", &s)?;
        }
        writeln!(f)?;
        writeln!(f, "transitions:")?;
        for s in self.states.iter() {
            for c in s.char_ranges() {
                let d = self.char_set_next(s, c).unwrap();
                writeln!(f, "  \u{03B4}({s}, {c}) = {d}")?;
            }
            if s.has_default_successor() {
                let d = s.default_successor().unwrap();
                writeln!(f, "  \u{03B4}({s}, ...) = {d}")?;
            }
        }
        writeln!(f)?;
        Ok(())
    }
}

impl<'a> Iterator for EdgeIterator<'a> {
    type Item = (ClassId, &'a State);

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.index;
        let source = self.state;
        if i < source.num_successors() {
            self.index += 1;
            let next_id = source.successor[i];
            Some((ClassId::Interval(i), &self.state_array[next_id]))
        } else if i == source.num_successors() && source.has_default_successor() {
            self.index += 1;
            let next_id = source.default_successor.unwrap();
            Some((ClassId::Complement, &self.state_array[next_id]))
        } else {
            None
        }
    }
}

impl<'a> Iterator for FinalStateIterator<'a> {
    type Item = &'a State;

    fn next(&mut self) -> Option<Self::Item> {
        let mut i = self.index;
        let a = self.state_array;
        while i < a.len() {
            if a[i].is_final {
                self.index = i + 1;
                return Some(&a[i]);
            }
            i += 1;
        }
        self.index = i;
        None
    }
}

#[derive(Debug)]
struct StateInConstruction {
    is_final: bool,
    default_successor: Option<usize>,
    transitions: Vec<(CharSet, usize)>,
}

impl StateInConstruction {
    fn new() -> StateInConstruction {
        StateInConstruction {
            is_final: false,
            default_successor: None,
            transitions: Vec::new(),
        }
    }

    fn set_default_successor(&mut self, next_id: usize) {
        self.default_successor = Some(next_id);
    }

    fn add_transition(&mut self, set: &CharSet, next_id: usize) {
        self.transitions.push((*set, next_id))
    }

    // choose a default successor for this state if there isn't one already
    fn choose_default_successor(&mut self) {
        // Boyer-Moore maj: first pass
        // assumes s is not empty
        fn maj_candidate(s: &[(CharSet, usize)]) -> usize {
            let mut maj = s[0].1;
            let mut k = 1;
            for (_, x) in &s[1..] {
                let x = *x;
                if k == 0 {
                    maj = x;
                    k = 1;
                } else if x == maj {
                    k += 1;
                } else {
                    k -= 1;
                }
            }
            maj
        }

        // number of occurrences of m in s
        fn count(s: &[(CharSet, usize)], m: usize) -> usize {
            let mut n = 0;
            for (_, x) in s {
                if *x == m {
                    n += 1;
                }
            }
            n
        }

        if self.default_successor.is_none() && !self.transitions.is_empty() {
            let m = maj_candidate(&self.transitions);
            let n = count(&self.transitions, m);
            if n >= self.transitions.len() / 2 {
                self.set_default_successor(m);
            }
        }
    }

    fn remove_transitions_to_default(&mut self) {
        if let Some(i) = self.default_successor {
            self.transitions.retain(|x| x.1 != i)
        }
    }

    fn cleanup(&mut self) {
        self.choose_default_successor();
        self.remove_transitions_to_default();
    }

    fn make_partition(&self) -> Result<CharPartition, Error> {
        CharPartition::try_from_iter(self.transitions.iter().map(|x| x.0))
    }

    fn make_successor(&self, p: &CharPartition) -> Box<[usize]> {
        let n = p.len();
        let mut result = vec![0; n];
        for s in &self.transitions {
            let c = s.0.pick();
            if let ClassId::Interval(i) = p.class_of_char(c) {
                result[i] = s.1;
            } else {
                panic!();
            }
        }
        result.into()
    }
}

///
/// Automaton builder
///
#[derive(Debug)]
pub struct AutomatonBuilder<T> {
    size: usize,
    id_map: HashMap<T, usize>,
    states: Vec<StateInConstruction>,
}

impl<T: Eq + Hash + Clone> AutomatonBuilder<T> {
    fn get_state_id(&mut self, state: &T) -> usize {
        match self.id_map.get(state) {
            Some(i) => *i,
            None => {
                let i = self.size;
                let new_state = StateInConstruction::new();
                self.states.push(new_state);
                self.id_map.insert(state.clone(), i);
                self.size += 1;
                i
            }
        }
    }

    ///
    /// Create a new builder
    ///
    /// - initial_state = initial state for the resulting automaton
    ///
    pub fn new(initial_state: &T) -> Self {
        let mut new = AutomatonBuilder {
            size: 0,
            id_map: HashMap::new(),
            states: Vec::new(),
        };
        new.get_state_id(initial_state);
        new
    }

    ///
    /// Mark a final state
    ///
    pub fn mark_final(&mut self, state: &T) -> &mut Self {
        let i = self.get_state_id(state);
        self.states[i].is_final = true;
        self
    }

    ///
    /// Set the default successor of a state
    ///
    pub fn set_default_successor(&mut self, state: &T, next: &T) -> &mut Self {
        let i = self.get_state_id(state);
        let j = self.get_state_id(next);
        self.states[i].set_default_successor(j);
        self
    }

    ///
    /// Add a transition
    ///
    pub fn add_transition(&mut self, state: &T, set: &CharSet, next: &T) -> &mut Self {
        let i = self.get_state_id(state);
        let j = self.get_state_id(next);
        self.states[i].add_transition(set, j);
        self
    }

    ///
    /// Construct an automaton
    /// - fails if a state `s` has non-deterministic transitions,
    ///   i.e., if two distinct transitions from s have non-disjoint labels (i.e., character sets).
    /// - fails if a state `s` has a default successor but its transitions
    ///   already cover the full alphabet.
    /// - fails if a state `s` doesn't have a default successor but its
    ///   transitions do not cover the full alphabet.
    ///
    pub fn build(&mut self) -> Result<Automaton, Error> {
        let n = self.size;
        let mut num_final_states = 0;
        let mut state_array = Vec::with_capacity(n);
        for (i, s) in self.states.iter_mut().enumerate() {
            s.cleanup();
            let p = s.make_partition()?;
            if s.default_successor.is_some() && p.empty_complement() {
                return Err(Error::EmptyComplementaryClass);
            }
            if s.default_successor.is_none() && !p.empty_complement() {
                return Err(Error::MissingDefaultSuccessor);
            }
            let successor = s.make_successor(&p);
            if s.is_final {
                num_final_states += 1;
            }
            let new_state = State {
                id: i,
                is_final: s.is_final,
                successor,
                classes: p,
                default_successor: s.default_successor,
            };
            state_array.push(new_state);
        }
        Ok(Automaton {
            num_states: n,
            num_final_states,
            initial_state: 0,
            states: state_array.into(),
        })
    }

    ///
    /// Build without checking
    ///
    pub fn build_unchecked(&mut self) -> Automaton {
        let num_states = self.size;
        let mut num_final_states = 0;
        let mut state_array = Vec::with_capacity(num_states);
        for (i, s) in self.states.iter_mut().enumerate() {
            s.cleanup();
            let p = s.make_partition().unwrap();
            let successor = s.make_successor(&p);
            if s.is_final {
                num_final_states += 1;
            }
            state_array.push(State {
                id: i,
                is_final: s.is_final,
                successor,
                classes: p,
                default_successor: s.default_successor,
            })
        }
        Automaton {
            num_states,
            num_final_states,
            initial_state: 0,
            states: state_array.into(),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::smt_strings::char_to_smt;

    use super::*;

    //
    // Test automaton:
    /// 5 states
    /// state 0 is the initial state
    /// state 3 is the only final state
    /// state 4 is a sink: all default transitions do to 4
    ///
    /// other transitions:
    //   0 --a--> 0
    //   0 --b--> 1
    //   0 --c--> 2
    //   1 --a--> 3
    //   1 --c--> 2
    //   2 --b--> 3
    //   2 --c--> 3
    //   3 --a--> 0
    //   3 --b--> 1
    //   3 --c--> 3
    //
    fn graph() -> Vec<(u32, char, u32)> {
        vec![
            (0, 'a', 0),
            (0, 'b', 1),
            (0, 'c', 2),
            (1, 'a', 3),
            (1, 'c', 2),
            (2, 'b', 3),
            (2, 'c', 3),
            (3, 'a', 0),
            (3, 'b', 1),
            (3, 'c', 3),
        ]
    }

    // Check that automaton is correct
    fn check_automaton(automaton: &Automaton) {
        assert_eq!(automaton.num_states(), 5);
        assert_eq!(automaton.initial_state().id, 0);
        assert_eq!(automaton.num_final_states(), 1);

        let s0 = automaton.state(0);
        assert_eq!(automaton.next(s0, 'a' as u32).id, 0);
        assert_eq!(automaton.next(s0, 'b' as u32).id, 1);
        assert_eq!(automaton.next(s0, 'c' as u32).id, 2);
        assert_eq!(automaton.next(s0, 'd' as u32).id, 4);
        assert!(!s0.is_final());

        let s1 = automaton.state(1);
        assert_eq!(automaton.next(s1, 'a' as u32).id, 3);
        assert_eq!(automaton.next(s1, 'c' as u32).id, 2);
        assert_eq!(automaton.next(s1, 'd' as u32).id, 4);
        assert!(!s1.is_final());

        let s2 = automaton.state(2);
        assert_eq!(automaton.next(s2, 'a' as u32).id, 4);
        assert_eq!(automaton.next(s2, 'b' as u32).id, 3);
        assert_eq!(automaton.next(s2, 'c' as u32).id, 3);
        assert_eq!(automaton.next(s2, 'd' as u32).id, 4);
        assert!(!s2.is_final());

        let s3 = automaton.state(3);
        assert_eq!(automaton.next(s3, 'a' as u32).id, 0);
        assert_eq!(automaton.next(s3, 'b' as u32).id, 1);
        assert_eq!(automaton.next(s3, 'c' as u32).id, 3);
        assert_eq!(automaton.next(s3, 'd' as u32).id, 4);
        assert!(s3.is_final());
    }

    #[test]
    fn test_builder() {
        let g = graph();
        let mut builder = AutomatonBuilder::new(&0);
        for (source, label, dest) in &g {
            builder.add_transition(source, &CharSet::singleton(*label as u32), dest);
        }
        builder
            .set_default_successor(&0, &4)
            .set_default_successor(&1, &4)
            .set_default_successor(&2, &4)
            .set_default_successor(&3, &4)
            .set_default_successor(&4, &4)
            .mark_final(&3);
        let automaton = builder.build().unwrap();

        println!(
            "Result automaton: {} states, initial state: {}",
            automaton.num_states(),
            automaton.initial_state()
        );
        for state in automaton.states.iter() {
            println!("State {state}");
            if state.is_final() {
                println!("  final");
            }
            match state.default_successor() {
                None => println!("  no default successor"),
                Some(x) => println!("  default successor: {x}"),
            }
            println!("  transitions:");
            for (cid, next) in automaton.edges(state) {
                println!("  delta({state}, {cid}) = {next}");
            }
        }

        println!("{automaton}");

        check_automaton(&automaton);

        let map = automaton.compile_successors();
        let alphabet = automaton.pick_alphabet();
        print!("Alphabet:");
        for c in &alphabet {
            print!(" {}", char_to_smt(*c));
        }
        println!();
        let alphabet_size = alphabet.len() as u32;
        for s in 0..automaton.num_states() as u32 {
            for c in 0..alphabet_size {
                let next = map.eval(s, c);
                let char = alphabet[c as usize];
                println!(
                    "  d({}, {}) = {}  <=>  \u{03B4}(s{}, {}) = s{}",
                    s,
                    c,
                    next,
                    s,
                    char_to_smt(char),
                    next
                );
            }
            println!();
        }

        println!("Compact transition map: {map}");

        automaton.test_minimizer();
    }

    #[test]
    fn test_remove_unreachable() {
        let g = graph();
        let mut builder = AutomatonBuilder::new(&0);

        // unreachable nodes
        builder.add_transition(&5, &CharSet::singleton('z' as u32), &6);
        builder.set_default_successor(&5, &8);
        builder.add_transition(&6, &CharSet::singleton('y' as u32), &5);
        builder.set_default_successor(&6, &8);
        builder.set_default_successor(&8, &5);
        builder.mark_final(&6);

        for (source, label, dest) in &g {
            builder.add_transition(source, &CharSet::singleton(*label as u32), dest);
        }
        builder
            .set_default_successor(&0, &4)
            .set_default_successor(&1, &4)
            .set_default_successor(&2, &4)
            .set_default_successor(&3, &4)
            .set_default_successor(&4, &4)
            .mark_final(&3);

        let mut automaton = builder.build().unwrap();

        println!(
            "Result automaton: {} states, initial state: {}",
            automaton.num_states(),
            automaton.initial_state()
        );

        assert_eq!(automaton.num_states(), 8);

        println!("{automaton}");

        automaton.remove_unreachable_states();
        println!(
            "After removing unreachable states: {} states, initial state: {}",
            automaton.num_states(),
            automaton.initial_state()
        );

        println!("{automaton}");
        check_automaton(&automaton);
    }

    #[test]
    fn test_minimizer() {
        let builder = &mut AutomatonBuilder::new(&0);

        // language abc(a*)
        builder.add_transition(&0, &CharSet::singleton('a' as u32), &1);
        builder.add_transition(&1, &CharSet::singleton('b' as u32), &2);
        builder.add_transition(&2, &CharSet::singleton('c' as u32), &3);

        // states 3, 4, 5 are equivalent
        builder.add_transition(&3, &CharSet::singleton('a' as u32), &4);
        builder.mark_final(&3);

        builder.add_transition(&4, &CharSet::singleton('a' as u32), &5);
        builder.mark_final(&4);

        builder.add_transition(&5, &CharSet::singleton('a' as u32), &3);
        builder.mark_final(&5);

        // add transitions to sink states 6, 7, 8
        builder.set_default_successor(&0, &6);
        builder.set_default_successor(&1, &7);
        builder.set_default_successor(&2, &7);
        builder.set_default_successor(&3, &8);
        builder.set_default_successor(&4, &6);
        builder.set_default_successor(&5, &7);

        // sink states 6, 7, 8 are equivalent
        builder.set_default_successor(&6, &7);
        builder.set_default_successor(&7, &8);
        builder.set_default_successor(&8, &6);

        let automaton = &mut builder.build().unwrap();

        println!(
            "Result automaton: {} states, initial state: {}",
            automaton.num_states(),
            automaton.initial_state()
        );
        println!("{automaton}");

        automaton.test_minimizer();

        automaton.minimize();
        println!(
            "\nAfter minimization: {} states, initial state: {}",
            automaton.num_states(),
            automaton.initial_state(),
        );
        println!("{automaton}");
    }
}
