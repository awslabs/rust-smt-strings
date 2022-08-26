// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Queue + set for breadth-first exploration of terms
//!

use std::{
    collections::{HashSet, VecDeque},
    hash::Hash,
};

///
/// A BfsQueue is a queue that doesn't contain duplicate elements.
/// - the push operation adds an element at the end of the queue
///   if this element hasn't been seen before. Otherwise, it's a no-op.
/// - the pop operations takes the element at the front of the queue
///   if the queue is not empty.
#[derive(Debug)]
pub struct BfsQueue<T> {
    queue: VecDeque<T>,
    set: HashSet<T>,
}

#[allow(dead_code)]
impl<T: Eq + Hash + Clone> BfsQueue<T> {
    ///
    /// Create a new queue with default capacity
    ///
    pub fn new() -> Self {
        BfsQueue {
            queue: VecDeque::new(),
            set: HashSet::new(),
        }
    }

    ///
    /// Create a new queue with initial capacity
    ///
    pub fn with_capacity(capacity: usize) -> Self {
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
    pub fn push(&mut self, element: T) -> bool {
        if self.set.insert(element.clone()) {
            self.queue.push_back(element);
            true
        } else {
            false
        }
    }

    ///
    /// Push all elements from an iterator
    ///
    pub fn push_all(&mut self, iter: impl IntoIterator<Item = T>) {
        for x in iter {
            self.push(x);
        }
    }

    ///
    /// Check whether the queue is empty
    ///
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    ///
    /// Size of the queue
    ///
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    ///
    /// Get the first element in the queue
    /// - return None if the queue is empty
    ///
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front()
    }
}
