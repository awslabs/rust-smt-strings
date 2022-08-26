// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//!
//! Search for a pattern in a string s. The pattern can be a string
//! or a regular expression.
//!

use crate::regular_expressions::*;

///
/// Result of a search for pattern p in string s:
///
/// NotFound -> no match
/// Found(i, j) -> s[i .. j-1] matches the pattern p
//
#[derive(Debug, PartialEq, Eq)]
pub enum SearchResult {
    Found(usize, usize),
    NotFound,
}

///
/// Search for the first occurrence of pattern in string starting from index k
///
/// - Return NotFound if pattern does not occur in string[k ... len(string) - 1]
/// - Return Found(i, j) if string[i ... j-1] equals pattern (so j = i+len(pattern))
/// and i is the smallest index >= k that satisfies these conditions
///
pub fn naive_search(pattern: &[u32], string: &[u32], k: usize) -> SearchResult {
    let p_len = pattern.len();
    let s_len = string.len();
    let mut i = k;
    while i + p_len <= s_len {
        let mut j = 0;
        while j < p_len && pattern[j] == string[i + j] {
            j += 1;
        }
        if j == p_len {
            return SearchResult::Found(i, i + p_len);
        }
        i += 1;
    }
    SearchResult::NotFound
}

///
/// Search for the first occurrence of a regular expression in a string starting from index k
/// - If allow_empty is true, an empty string may be returned (if the pattern contains the
///   empty string)
/// - The index k must be less than sting.len()
///
/// - Return NotFound if pattern does not occur in string[k ... len(string) - 1]
/// - Return Found(i, j) if string[i ... j-1] matches the pattern
///   and i is the smallest index >= k that satisfies these conditions
///
pub fn naive_re_search(
    manager: &mut ReManager,
    pattern: RegLan,
    string: &[u32],
    k: usize,
    allow_empty: bool,
) -> SearchResult {
    if allow_empty && pattern.nullable {
        return SearchResult::Found(k, k);
    }
    let s_len = string.len();
    let mut i = k;
    while i < s_len {
        // check for a non-empty match starting at index i
        let mut j = i;
        let mut p = pattern;
        while j < s_len {
            // p = derivative(pattern, string[i .. j))
            // if p is nullable: found a match
            // if p is empty: no extension of string[i .. j] can match
            p = manager.char_derivative(p, string[j]);
            if p.nullable {
                return SearchResult::Found(i, j + 1);
            }
            if p.is_empty() {
                break;
            }
            j += 1;
        }
        i += 1;
    }
    SearchResult::NotFound
}
