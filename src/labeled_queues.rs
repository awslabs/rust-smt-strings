// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Queues for breadth-first exploration of labeled graphs
//!

use std::{
    collections::{HashMap, VecDeque},
    hash::Hash,
};

//
// Record to track predecessor
// the predecessor of a node N is either Empty (for the root node)
// or a pair (Label, Node).
//
#[derive(Debug)]
pub enum Edge<T, L> {
    Empty,
    Pred(L, T),
}

///
/// Labeled queue to explore a graph from a root
/// - T: type of nodes
/// - L: type of labels
///
/// For every node N that's been visited (except the root), we keep
/// a pair (label, predecessor), where the predecessor is a node
/// on a path from the root to N.
///
#[derive(Debug)]
pub struct LabeledQueue<T, L> {
    queue: VecDeque<T>,
    map: HashMap<T, Edge<T, L>>,
}

// iterator: goes through edges from source to a destination
// node in reverse order.
#[derive(Debug)]
struct EdgeIterator<'a, T, L> {
    queue: &'a LabeledQueue<T, L>,
    last_edge: &'a Edge<T, L>,
}

impl<'a, T: Eq + Hash + Clone, L: Clone> Iterator for EdgeIterator<'a, T, L> {
    type Item = (&'a T, &'a L);

    fn next(&mut self) -> Option<Self::Item> {
        match self.last_edge {
            Edge::Empty => None,
            Edge::Pred(label, node) => {
                self.last_edge = self.queue.map.get(node).unwrap();
                Some((node, label))
            }
        }
    }
}

#[allow(dead_code)]
impl<T: Eq + Hash + Clone, L: Clone> LabeledQueue<T, L> {
    ///
    /// Initialize to explore from a root
    ///
    pub fn new(root: T) -> Self {
        let mut queue = VecDeque::new();
        let mut map = HashMap::new();
        queue.push_back(root.clone());
        map.insert(root, Edge::Empty);
        LabeledQueue { queue, map }
    }

    ///
    /// Push a successor of a node into the queue
    /// - no effect if the node has been visited before
    /// - otherwise, record that node is reachable from pre via label.
    /// - return true if this node is new, false otherwise
    ///
    pub fn push(&mut self, pre: T, label: L, suc: T) -> bool {
        match self.map.get(&suc) {
            Some(..) => false,
            None => {
                self.queue.push_back(suc.clone());
                self.map.insert(suc, Edge::Pred(label, pre));
                true
            }
        }
    }

    ///
    /// Push successors of a node
    /// - iter must produce pairs (Label, Successor node)
    ///
    pub fn push_all(&mut self, pre: T, iter: impl Iterator<Item = (L, T)>) {
        for (label, successor) in iter {
            self.push(pre.clone(), label, successor);
        }
    }

    ///
    /// Check whether the queue is empty
    ///
    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    ///
    /// Get the node first in the queue
    ///
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front()
    }

    ///
    /// Check whether a node has been visited
    ///
    pub fn visited(&self, node: &T) -> bool {
        self.map.contains_key(node)
    }

    /// Iterator list of edges from source to e in reverse order
    /// Edge e is included (first element produced by the iterator)
    fn edge_iter<'a>(&'a self, e: &'a Edge<T, L>) -> EdgeIterator<'a, T, L> {
        EdgeIterator {
            queue: self,
            last_edge: e,
        }
    }

    ///
    /// Build path label: e = last edge on the path
    ///
    fn labels_on_path(&self, e: &Edge<T, L>) -> Vec<L> {
        let mut result: Vec<L> = self
            .edge_iter(e)
            .map(|(_node, label)| label.clone())
            .collect();
        result.reverse();
        result
    }

    ///
    /// Build path of pairs (node, labels): e = last edge on the path
    ///
    fn make_path(&self, e: &Edge<T, L>) -> Vec<(T, L)> {
        let mut result: Vec<(T, L)> = self
            .edge_iter(e)
            .map(|(node, label)| (node.clone(), label.clone()))
            .collect();
        result.reverse();
        result
    }

    ///
    /// Path from the root to a node
    /// - return None if the node has not been visited
    /// - return a list of labels for the path from root to node
    ///   otherwise
    ///
    pub fn path(&self, node: &T) -> Option<Vec<L>> {
        self.map.get(node).map(|e| self.labels_on_path(e))
    }

    /// Same as path but requires node to be visited.
    /// - panics is the node has not been visited.
    pub fn path_unchecked(&self, node: &T) -> Vec<L> {
        let e = self.map.get(node).unwrap();
        self.labels_on_path(e)
    }

    ///
    /// Full path from the root to a destination node
    /// - return None if the destination has not been visited
    /// - return a list of pairs (node, label) otherwise
    /// - the list describes the path from the root to destination:
    ///   - if destination = root, the list is empty
    ///   - otherwise, the list is of the form
    ///     (n<sub>0</sub>, l<sub>0</sub>) ... (n<sub>k</sub>, l<sub>k</sub>)
    ///     where
    ///     1) n<sub>0</sub> is the root
    ///     2) n<sub>i+1</sub> is reachable from n<sub>i</sub> via an
    ///        edge of label l<sub>i</sub>.
    ///     3) destination is reachable from n<sub>k</sub> via an
    ///        edge of label l<sub>k</sub>
    ///
    /// Note: the destination node is not included in this list.
    ///
    pub fn full_path(&self, destination: &T) -> Option<Vec<(T, L)>> {
        self.map.get(destination).map(|e| self.make_path(e))
    }

    pub fn full_path_unchecked(&self, destination: &T) -> Vec<(T, L)> {
        let e = self.map.get(destination).unwrap();
        self.make_path(e)
    }
}

#[cfg(test)]
mod test {
    use std::fmt::Display;

    use super::*;

    #[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
    struct Node(u32);

    impl Display for Node {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "n{}", self.0)
        }
    }

    #[derive(Debug, Clone, Copy)]
    struct Label(char);

    impl Display for Label {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.0.fmt(f)
        }
    }

    //
    // Test graph:
    //  0 --a--> 0
    //  0 --b--> 1
    //  0 --c--> 2
    //  1 --a--> 3
    //  1 --c--> 2
    //  2 --b--> 3
    //  2 --c--> 3
    //  3 --a--> 0
    //  3 --b--> 1
    //  3 --c--> 3
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

    fn cycle() -> Vec<(u32, char, u32)> {
        vec![
            (0, 'a', 1),
            (1, 'b', 2),
            (2, 'c', 3),
            (3, 'd', 4),
            (4, 'e', 5),
            (5, 'f', 0),
        ]
    }

    fn successors(node: u32, graph: &[(u32, char, u32)]) -> impl Iterator<Item = (char, u32)> + '_ {
        graph
            .iter()
            .filter(move |(x, _, _)| *x == node)
            .map(|x| (x.1, x.2))
    }

    fn explore_graph(num_nodes: u32, graph: &[(u32, char, u32)]) {
        for i in 0..num_nodes {
            let root = Node(i);
            let mut queue: LabeledQueue<Node, Label> = LabeledQueue::new(root);

            while !queue.is_empty() {
                let n = queue.pop().unwrap();
                for (l, s) in successors(n.0, graph) {
                    queue.push(n, Label(l), Node(s));
                }
            }

            println!("Paths from root n{i}");
            for j in 0..num_nodes {
                match queue.path(&Node(j)) {
                    None => {
                        println!("n{j} is not reachable");
                    }
                    Some(p) => {
                        print!("n{j} is reachable via path (");
                        for l in &p {
                            print!("{l}");
                        }
                        println!(")");

                        let full = queue.full_path_unchecked(&Node(j));
                        print!("   ");
                        for (n, l) in &full {
                            print!("{n}--{l}--");
                        }
                        println!("{}", Node(j));
                    }
                }
            }
            println!()
        }
    }

    #[test]
    fn test() {
        println!("\nTest graph");
        explore_graph(5, &graph());
        println!("\nCycle of 6 nodes");
        explore_graph(6, &cycle());
    }
}
