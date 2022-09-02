// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Store for hash-consing.
//! Map keys -> &'static T
//! The store can also be used to assign a unique id to each object.
//!

use std::{
    collections::{hash_map::Entry, HashMap},
    hash::Hash,
};

///
/// Objects that can be hash-consed must implement this trait
///
/// Key is a key/signature type for the hash-consed objects.
/// Each key must be unique to the object.
/// make(&k) must construct a full object of key k
///
pub trait HashConsed {
    /// Key type
    type Key: Eq + Hash + Clone;
    /// Object constructor
    fn make(index: usize, k: &Self::Key) -> Self;
}

///
/// Store
///
#[derive(Debug, Default)]
pub struct Store<T: HashConsed + 'static> {
    map: HashMap<T::Key, &'static T>,
    /// number of elements in the store
    pub counter: usize,
}

#[allow(dead_code)]
impl<T: HashConsed + 'static> Store<T> {
    /// Create an empty store
    pub fn new() -> Store<T> {
        Store {
            map: HashMap::new(),
            counter: 0,
        }
    }

    /// Check emptiness
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Number of elements stored
    pub fn len(&self) -> usize {
        self.counter
    }

    /// Get the object defined by key k
    /// Return an existing object if there's one
    /// Create a fresh object and return it otherwise
    #[allow(clippy::many_single_char_names)]
    pub fn make(&mut self, k: T::Key) -> &'static T {
        match self.map.entry(k) {
            Entry::Occupied(o) => o.get(),
            Entry::Vacant(e) => {
                let i = self.counter;
                let new_obj = T::make(i, e.key());
                self.counter += 1;
                let b = Box::new(new_obj);
                let p = Box::leak(b);
                e.insert(p)
            }
        }
    }

    /// Iterator
    pub fn iter(&self) -> impl Iterator<Item = &&'static T> {
        self.map.values()
    }
}

#[cfg(test)]
mod test_store {
    use super::*;
    use std::cmp::max;

    #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
    enum Operator {
        Plus,
        Minus,
        Times,
        Negate,
    }

    type Node = &'static FullNode;

    #[derive(Debug, Clone)]
    enum BaseNode {
        Leaf(i32),
        Node(Operator, Box<[Node]>),
    }

    #[derive(Debug)]
    struct FullNode {
        node: BaseNode,
        id: usize,
        height: usize,
        size: usize,
    }

    impl PartialEq for BaseNode {
        fn eq(&self, other: &Self) -> bool {
            fn equal_nodes(v: &[Node], u: &[Node]) -> bool {
                if v.len() != u.len() {
                    return false;
                }
                for i in 0..v.len() {
                    if v[i].id != u[i].id {
                        return false;
                    }
                }
                true
            }

            match (self, other) {
                (BaseNode::Leaf(x), BaseNode::Leaf(y)) => x == y,
                (BaseNode::Node(op1, children1), BaseNode::Node(op2, children2)) => {
                    op1 == op2 && equal_nodes(children1, children2)
                }
                _ => false,
            }
        }
    }

    impl Eq for BaseNode {}

    impl Hash for BaseNode {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            match self {
                BaseNode::Leaf(x) => {
                    312941.hash(state);
                    x.hash(state);
                }
                BaseNode::Node(op, children) => {
                    489894.hash(state);
                    op.hash(state);
                    for &x in children.as_ref() {
                        x.id.hash(state);
                    }
                }
            }
        }
    }

    impl PartialEq for FullNode {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }

    impl Eq for FullNode {}

    impl PartialOrd for FullNode {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.id.partial_cmp(&other.id)
        }
    }

    impl Ord for FullNode {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.id.cmp(&other.id)
        }
    }

    impl std::fmt::Display for Operator {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Plus => write!(f, "+"),
                Self::Minus => write!(f, "-"),
                Self::Times => write!(f, "*"),
                Self::Negate => write!(f, "neg"),
            }
        }
    }

    impl std::fmt::Display for BaseNode {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Leaf(x) => write!(f, "(leaf {})", x),
                Self::Node(op, children) => {
                    write!(f, "({}", op)?;
                    for &child in children.as_ref() {
                        write!(f, " node{}", child.id)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }

    impl std::fmt::Display for FullNode {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "[{}, id = {}, height = {}, size = {}]",
                self.node, self.id, self.height, self.size
            )
        }
    }

    fn max_height(v: &[Node]) -> usize {
        v.iter().fold(0, |x, &y| max(x, y.height))
    }

    fn full_size(v: &[Node]) -> usize {
        v.iter().fold(0, |x, &y| x + y.height)
    }

    impl BaseNode {
        fn height(&self) -> usize {
            match self {
                BaseNode::Leaf(_) => 0,
                BaseNode::Node(_, children) => 1 + max_height(children),
            }
        }

        fn size(&self) -> usize {
            match self {
                BaseNode::Leaf(_) => 0,
                BaseNode::Node(_, children) => 1 + full_size(children),
            }
        }

        fn leaf(x: i32) -> Self {
            BaseNode::Leaf(x)
        }

        fn plus(children: &[Node]) -> Self {
            if children.is_empty() {
                BaseNode::leaf(0)
            } else {
                let mut v = children.to_vec();
                v.sort_unstable();
                BaseNode::Node(Operator::Plus, v.into_boxed_slice())
            }
        }

        fn times(children: &[Node]) -> Self {
            if children.is_empty() {
                BaseNode::leaf(1)
            } else {
                let mut v = children.to_vec();
                v.sort_unstable();
                BaseNode::Node(Operator::Times, v.into_boxed_slice())
            }
        }

        fn negate(child: Node) -> Self {
            BaseNode::Node(Operator::Negate, Box::new([child]))
        }

        fn minus(left: Node, right: Node) -> Self {
            BaseNode::Node(Operator::Minus, Box::new([left, right]))
        }
    }

    impl HashConsed for FullNode {
        type Key = BaseNode;

        fn make(index: usize, k: &Self::Key) -> Self {
            FullNode {
                node: k.clone(),
                id: index,
                height: k.height(),
                size: k.size(),
            }
        }
    }

    impl Store<FullNode> {
        fn leaf(&mut self, x: i32) -> Node {
            self.make(BaseNode::leaf(x))
        }

        fn minus(&mut self, left: Node, right: Node) -> Node {
            self.make(BaseNode::minus(left, right))
        }

        fn plus(&mut self, args: &[Node]) -> Node {
            self.make(BaseNode::plus(args))
        }

        fn times(&mut self, args: &[Node]) -> Node {
            self.make(BaseNode::times(args))
        }

        fn negate(&mut self, arg: Node) -> Node {
            self.make(BaseNode::negate(arg))
        }
    }

    #[test]
    fn build_a_store() {
        let mut store: Store<FullNode> = Store::new();

        let zero = store.leaf(0);
        let one = store.leaf(1);
        let test = store.leaf(1);

        assert_eq!(store.len(), 2);

        println!("Size of a BaseNode: {}", std::mem::size_of::<BaseNode>());
        println!("Size of a FullNode: {}", std::mem::size_of::<FullNode>());
        println!("Size of a Node: {}", std::mem::size_of::<Node>());

        assert_eq!(one, test);
        assert_ne!(one, zero);

        assert_eq!(one.id, test.id);
        assert_ne!(one.id, zero.id);

        let test = store.minus(one, one);

        assert_eq!(store.len(), 3);

        let test2 = store.plus(&[test, one, one]);
        let test3 = store.plus(&[one, test, one]);
        let test4 = store.plus(&[one, one, test]);

        println!("test2 = {:p}", test2);
        println!("test3 = {:p}", test3);
        println!("test4 = {:p}", test4);

        assert_eq!(test2, test3);
        assert_eq!(test3, test4);

        assert_eq!(test2.id, test3.id);
        assert_eq!(test3.id, test4.id);

        let test5 = store.times(&[test2, test2]);
        let test6 = store.negate(test5);

        assert_ne!(test6.id, test2.id);

        for &full_node in store.iter() {
            println!("node{} = {}", full_node.id, full_node);
        }
    }
}
