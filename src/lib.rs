// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Support for manipulating SMT-style strings and regular expressions
//!
//! # Overview
//!
//! This crate includes support for building and operating on string constants
//! and regular expressions as defined in the SMT-LIB theory of strings:
//! <http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>.
//!
//! The [smt_strings](crate::smt_strings) module implements the SMT-LIB functions defined
//! in the theory that do not use regular expressions.
//!
//! The [smt_regular_expressions](crate::smt_regular_expressions) module implements the
//! SMT-LIB functions of that operate on regular expressions.
//!
//! The crate also provides utilities for compiling regular expressions to
//! deterministic finite-state automata, computing the derivatives of a regular expressions,
//! checking whether a regular expression is empty, and so forth.
//!
//! Module [regular_expressions](crate::regular_expressions) implements regular expression
//! constructs, derivatives, and conversion to automata. Module [automata](crate::automata)
//! provides functions for constructing and minimizing automata.
//!

#![warn(missing_docs, missing_debug_implementations, rust_2018_idioms)]

pub mod automata;
pub mod character_sets;
pub mod errors;
pub mod loop_ranges;
pub mod regular_expressions;
pub mod smt_regular_expressions;
pub mod smt_strings;

mod bfs_queues;
mod compact_tables;
mod fast_sets;
mod labeled_queues;
mod matcher;
mod minimizer;
mod partitions;
mod store;
