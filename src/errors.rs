// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Error codes
//!

use std::fmt::Display;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
///
/// Error codes produced by operations on partitions and regular expressions
///
pub enum Error {
    /// The derivative of R with respect to a character set  C is not defined.
    ///
    /// This means that C is not included in a derivative class of R (i.e., it
    /// overlaps several classes).
    UndefinedDerivative,

    /// The complementary class of a regular expression R is empty
    ///
    /// The deriv classes of R consists of a set of disjoint
    /// character intervals C<sub>0</sub>, ... C<sub>n-1</sub> and an implicit complementary
    /// class equal to complement (Union(C<sub>0</sub>, ..., C<sub>n-1</sub>)).
    /// It's an error to try to compute the derivative of R with respect
    /// to the complementary class if it is empty.
    EmptyComplementaryClass,

    /// The class id of a [CharSet][crate::character_sets::CharSet] `s` in a
    /// [CharPartition][crate::character_sets::CharPartition] `p` is not defined.
    ///
    /// This means that `s` overlaps a class of `p` but is not contained in that class.
    AmbiguousCharSet,

    /// Bad class id for a [CharPartition][crate::character_sets::CharPartition].
    ///
    /// A bad class id is either of the form `ClassId::Interval(i)` where `i` is out of bound,
    /// or `ClassId::Complement` where the complementary class is empty.
    BadClassId,

    /// Error reported where a list of disjoint char sets is expected.
    NonDisjointCharSets,

    /// No default successor specified for an automaton state when one is required.
    MissingDefaultSuccessor,
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Self::UndefinedDerivative => "undefined derivative",
            Self::EmptyComplementaryClass => "empty complementary class",
            Self::AmbiguousCharSet => "character set not contained in a single partition class",
            Self::BadClassId => "bad class id",
            Self::NonDisjointCharSets => "expected disjoint character sets",
            Self::MissingDefaultSuccessor => "a default successor is required",
        }
        .fmt(f)
    }
}

impl std::error::Error for Error {}
