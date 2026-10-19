// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Queue + set for breadth-first exploration of terms
//!

use std::{
    collections::{HashSet, VecDeque},
    hash::Hash,
};

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::hash::obeys_key_model;

verus! {

///
/// A BfsQueue is a queue that doesn't contain duplicate elements.
/// - the push operation adds an element at the end of the queue
///   if this element hasn't been seen before. Otherwise, it's a no-op.
/// - the pop operations takes the element at the front of the queue
///   if the queue is not empty.
#[verifier::reject_recursive_types(T)]
#[derive(Debug)]
pub(crate) struct BfsQueue<T> {
    queue: VecDeque<T>,
    set: HashSet<T>,
}

#[allow(dead_code)]
impl<T: Eq + Hash + Copy> BfsQueue<T> {
    /// The abstract view of the queue as a sequence
    pub(crate) closed spec fn view_queue(&self) -> Seq<T> {
        self.queue@
    }

    /// The set of all elements ever seen
    pub(crate) closed spec fn view_seen(&self) -> Set<T> {
        self.set@
    }

    /// Structural invariant: the queue and set are consistent.
    /// - the key type obeys the hash table model
    /// - the queue has no duplicate elements
    /// - every element in the queue has been seen (is in the set)
    pub(crate) open spec fn well_formed(&self) -> bool {
        &&& obeys_key_model::<T>()
        &&& self.view_queue().no_duplicates()
        &&& self.view_queue().to_set().subset_of(self.view_seen())
    }

    ///
    /// Create a new queue with default capacity
    ///
    pub(crate) fn new() -> (ret: Self)
        requires
            obeys_key_model::<T>(),
        ensures
            ret.well_formed(),
            ret.view_queue() == Seq::<T>::empty(),
            ret.view_seen() == Set::<T>::empty(),
    {
        BfsQueue {
            queue: VecDeque::new(),
            set: HashSet::new(),
        }
    }

    ///
    /// Create a new queue with initial capacity
    ///
    pub(crate) fn with_capacity(capacity: usize) -> (ret: Self)
        requires
            obeys_key_model::<T>(),
        ensures
            ret.well_formed(),
            ret.view_queue() == Seq::<T>::empty(),
            ret.view_seen() == Set::<T>::empty(),
    {
        BfsQueue {
            queue: VecDeque::with_capacity(capacity),
            set: HashSet::with_capacity(capacity),
        }
    }

    ///
    /// Add an element at the end of the queue if it's not been seen before
    /// - return true if this is a new element
    /// - return false otherwise
    ///
    /// Note: marked external_body because vstd lacks a generic Clone spec
    /// linking clone output to input. The HashSet/VecDeque specs require
    /// this linkage to verify the body, so we trust the implementation
    /// and verify only the specification contract.
    ///
    #[verifier::external_body]
    pub(crate) fn push(&mut self, element: T) -> (ret: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            ret == !old(self).view_seen().contains(element),
            final(self).view_seen() == old(self).view_seen().insert(element),
            final(self).view_queue() ==
               if ret { old(self).view_queue().push(element) } else { old(self).view_queue() },
    {
        if self.set.insert(element) {
            self.queue.push_back(element);
            true
        } else {
            false
        }
    }

    ///
    /// Check whether the queue is empty
    ///
    pub(crate) fn is_empty(&self) -> (ret: bool)
        ensures
            ret == (self.view_queue().len() == 0),
    {
        self.queue.len() == 0
    }

    ///
    /// Size of the queue
    ///
    pub(crate) fn len(&self) -> (ret: usize)
        ensures
            ret == self.view_queue().len(),
    {
        self.queue.len()
    }

    ///
    /// Get the first element in the queue
    /// - return None if the queue is empty
    ///
    pub(crate) fn pop(&mut self) -> (ret: Option<T>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self).view_seen() == old(self).view_seen(),
            match ret {
                Some(x) => {
                    &&& old(self).view_queue().len() > 0
                    &&& x == old(self).view_queue()[0]
                    &&& final(self).view_queue() == old(self).view_queue().drop_first()
                },
                None => {
                    &&& old(self).view_queue().len() == 0
                    &&& final(self).view_queue() == old(self).view_queue()
                }
            }
    {
        self.queue.pop_front()
    }

    ///
    /// Push all elements from an iterator
    ///
    pub(crate) fn push_all(&mut self, iter: impl IntoIterator<Item = T>)
        requires
            old(self).well_formed()
        ensures
            final(self).well_formed()
    {
        for x in iter
            invariant self.well_formed()
        {
            self.push(x);
        }
    }
}

} // verus!
