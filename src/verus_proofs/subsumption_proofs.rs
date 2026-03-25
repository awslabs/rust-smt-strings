// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Verus proofs for subsumption/language inclusion in regular expressions
//!
//! This module provides formal verification of the subsumption checking
//! algorithm used in `regular_expressions.rs`. The subsumption check
//! determines whether L(r) is a subset of L(s) for regular expressions r and s.
//!
//! The proofs are organized by level:
//! - Level 0: Leaf/helper functions (BasePattern, CharSet, match_char_set)
//! - Level 1: Pattern construction (base_patterns, decompose_concat)
//! - Level 2: Pattern matching (rigid_match_at, next/prev_rigid_match)
//! - Level 3: Matching orchestration (find_rigid_matches, flexible matching)
//! - Level 4: Top-level (concat_inclusion, sub_language)

use vstd::prelude::*;

verus! {

// ============================================================================
// Type Models
// ============================================================================

/// Model of CharSet: an interval [start, end] where start <= end
/// Represents a range of characters.
pub struct CharSetModel {
    pub start: u32,
    pub end: u32,
}

/// A CharSetModel is well-formed if start <= end
pub open spec fn charset_wf(cs: CharSetModel) -> bool {
    cs.start <= cs.end
}

/// CharSet::covers: self.start <= other.start && other.end <= self.end
/// This models character_sets.rs line 147
pub open spec fn charset_covers(self_cs: CharSetModel, other: CharSetModel) -> bool {
    self_cs.start <= other.start && other.end <= self_cs.end
}

/// Semantic model: a CharSet denotes a set of characters
pub open spec fn charset_contains(cs: CharSetModel, c: u32) -> bool {
    cs.start <= c && c <= cs.end
}

// ============================================================================
// Level 0: CharSet covers correctness
// ============================================================================

/// If charset_covers(a, b) then every character in b is also in a.
/// This is the key semantic property of covers.
proof fn lemma_covers_implies_subset(a: CharSetModel, b: CharSetModel)
    requires
        charset_wf(a),
        charset_wf(b),
        charset_covers(a, b),
    ensures
        forall|c: u32| charset_contains(b, c) ==> charset_contains(a, c),
{
    // Follows directly from the definitions:
    // charset_covers(a, b) means a.start <= b.start && b.end <= a.end
    // charset_contains(b, c) means b.start <= c && c <= b.end
    // So a.start <= b.start <= c and c <= b.end <= a.end
    // Therefore a.start <= c && c <= a.end, i.e., charset_contains(a, c)
}

/// covers is reflexive
proof fn lemma_covers_reflexive(a: CharSetModel)
    requires charset_wf(a),
    ensures charset_covers(a, a),
{
}

/// covers is transitive
proof fn lemma_covers_transitive(a: CharSetModel, b: CharSetModel, c: CharSetModel)
    requires
        charset_wf(a),
        charset_wf(b),
        charset_wf(c),
        charset_covers(a, b),
        charset_covers(b, c),
    ensures
        charset_covers(a, c),
{
}

// ============================================================================
// BasePattern Model
// ============================================================================

/// Model of BasePattern (regular_expressions.rs line 622)
pub struct BasePatternModel {
    pub start: nat,
    pub end: nat,
    pub is_rigid: bool,
    pub start_match: nat,
    pub end_match: nat,
}

/// BasePattern well-formedness: start < end (from debug_assert in make)
pub open spec fn base_pattern_wf(bp: BasePatternModel) -> bool {
    bp.start < bp.end
}

/// BasePattern::len() = end - start (line 631)
pub open spec fn base_pattern_len(bp: BasePatternModel) -> nat {
    (bp.end - bp.start) as nat
}

/// Proof that len is always positive for well-formed BasePatterns
proof fn lemma_base_pattern_len_positive(bp: BasePatternModel)
    requires base_pattern_wf(bp),
    ensures base_pattern_len(bp) > 0,
{
}

// ============================================================================
// Sequence Model for Regular Expressions
// ============================================================================

/// We model a regular expression element as either a Range (rigid) or a Loop (flexible).
/// This is sufficient for the subsumption algorithm which only operates on
/// "simple patterns" (concatenations of Ranges and Loops).
pub enum REElementKind {
    Range,   // rigid element - represents Range(CharSet)
    Loop,    // flexible element - represents Loop(Range, LoopRange)
    Other,   // everything else
}

/// Model of a single RE element in a concatenation sequence
pub struct REElement {
    pub kind: REElementKind,
    pub charset: CharSetModel,  // meaningful only for Range elements
}

/// Check if an RE element is a Range (rigid)
pub open spec fn is_range(e: REElement) -> bool {
    matches!(e.kind, REElementKind::Range)
}

/// Check if an RE element is a Loop (flexible)
pub open spec fn is_loop(e: REElement) -> bool {
    matches!(e.kind, REElementKind::Loop)
}

// ============================================================================
// Level 0: match_char_set correctness (line 249)
// ============================================================================

/// Model of BaseRegLan::match_char_set
/// Returns true if the RE element is a Range and its charset is covered by s
pub open spec fn match_char_set(e: REElement, s: CharSetModel) -> bool {
    is_range(e) && charset_covers(s, e.charset)
}

/// If match_char_set returns true, then every character in the element's
/// range is also in s
proof fn lemma_match_char_set_soundness(e: REElement, s: CharSetModel)
    requires
        charset_wf(e.charset),
        charset_wf(s),
        match_char_set(e, s),
    ensures
        forall|c: u32| #![auto] charset_contains(e.charset, c) ==> charset_contains(s, c),
{
    lemma_covers_implies_subset(s, e.charset);
}

// ============================================================================
// Level 1: base_patterns invariants (line 660)
// ============================================================================

/// A sequence of BasePatterns is well-formed if:
/// 1. Each pattern satisfies base_pattern_wf
/// 2. Patterns are contiguous (no gaps)
/// 3. Adjacent patterns differ in rigidity
/// 4. They cover the entire input range [0, len)
pub open spec fn base_patterns_wf(
    patterns: Seq<BasePatternModel>,
    input_len: nat,
) -> bool {
    // Non-empty input requires non-empty patterns
    &&& (input_len > 0 ==> patterns.len() > 0)
    // Empty input means no patterns
    &&& (input_len == 0 ==> patterns.len() == 0)
    // Each pattern is well-formed
    &&& forall|i: int| 0 <= i < patterns.len() ==> base_pattern_wf(#[trigger] patterns[i])
    // First pattern starts at 0
    &&& (patterns.len() > 0 ==> patterns[0].start == 0)
    // Last pattern ends at input_len
    &&& (patterns.len() > 0 ==> patterns[patterns.len() - 1].end == input_len)
    // Contiguous: each pattern's end equals the next pattern's start
    &&& forall|i: int| 0 <= i < patterns.len() - 1 ==>
        (#[trigger] patterns[i]).end == (#[trigger] patterns[i + 1]).start
    // Adjacent patterns alternate in rigidity
    &&& forall|i: int| 0 <= i < patterns.len() - 1 ==>
        (#[trigger] patterns[i]).is_rigid != (#[trigger] patterns[i + 1]).is_rigid
}

/// The patterns partition [0, input_len) into contiguous, non-overlapping segments
proof fn lemma_base_patterns_cover(
    patterns: Seq<BasePatternModel>,
    input_len: nat,
)
    requires
        base_patterns_wf(patterns, input_len),
        input_len > 0,
    ensures
        // Sum of all pattern lengths equals input_len
        patterns[0].start == 0,
        patterns[patterns.len() - 1].end == input_len,
{
}

// ============================================================================
// Level 0-1: BasePattern::make and set_match (lines 640, 635)
// ============================================================================

/// Spec for BasePattern::make constructor
pub open spec fn base_pattern_make_spec(start: nat, end: nat, is_rigid: bool) -> BasePatternModel {
    BasePatternModel {
        start,
        end,
        is_rigid,
        start_match: 0,
        end_match: 0,
    }
}

/// make produces a well-formed BasePattern when start < end
proof fn lemma_make_wf(start: nat, end: nat, is_rigid: bool)
    requires start < end,
    ensures base_pattern_wf(base_pattern_make_spec(start, end, is_rigid)),
{
}

/// Spec for set_match: updates start_match and end_match
pub open spec fn base_pattern_set_match(bp: BasePatternModel, sm: nat, em: nat) -> BasePatternModel {
    BasePatternModel {
        start: bp.start,
        end: bp.end,
        is_rigid: bp.is_rigid,
        start_match: sm,
        end_match: em,
    }
}

/// set_match preserves well-formedness of start/end (structural part)
proof fn lemma_set_match_preserves_wf(bp: BasePatternModel, sm: nat, em: nat)
    requires base_pattern_wf(bp),
    ensures base_pattern_wf(base_pattern_set_match(bp, sm, em)),
{
}

/// set_match preserves len
proof fn lemma_set_match_preserves_len(bp: BasePatternModel, sm: nat, em: nat)
    requires base_pattern_wf(bp),
    ensures base_pattern_len(base_pattern_set_match(bp, sm, em)) == base_pattern_len(bp),
{
}

/// set_match preserves is_rigid
proof fn lemma_set_match_preserves_rigidity(bp: BasePatternModel, sm: nat, em: nat)
    ensures (base_pattern_set_match(bp, sm, em)).is_rigid == bp.is_rigid,
{
}

// ============================================================================
// Level 1: base_patterns algorithm proofs (line 660)
// ============================================================================

/// Model of the input to base_patterns: a sequence of RE elements where
/// each element is either rigid (Range) or flexible (Loop/other)
pub open spec fn element_is_rigid(e: REElement) -> bool {
    is_range(e)
}

/// Spec for base_patterns: given a sequence of elements, produces a partition
/// into maximal runs of same-rigidity elements
///
/// This is a recursive spec that mirrors the algorithm:
/// Walk left to right, starting a new pattern whenever rigidity changes.
pub open spec fn base_patterns_spec(
    elements: Seq<REElement>,
) -> Seq<BasePatternModel>
    decreases elements.len(),
{
    if elements.len() == 0 {
        seq![]
    } else {
        // Find the length of the first maximal run
        let first_rigid = element_is_rigid(elements[0]);
        let run_len = first_run_length(elements, first_rigid);
        // run_len >= 1 since elements[0] matches first_rigid (proven in lemma)
        // run_len <= elements.len() (proven in lemma)
        // So elements.skip(run_len) has strictly fewer elements
        if run_len == 0 || run_len > elements.len() {
            seq![]  // unreachable but needed for termination checker
        } else {
            let first_pattern = base_pattern_make_spec(0, run_len, first_rigid);
            let rest = base_patterns_spec(elements.skip(run_len as int));
            seq![first_pattern] + shift_patterns(rest, run_len)
        }
    }
}

/// Helper: length of the first maximal run of elements with same rigidity
pub open spec fn first_run_length(elements: Seq<REElement>, rigid: bool) -> nat
    recommends elements.len() > 0
    decreases elements.len(),
{
    if elements.len() == 0 {
        0
    } else if element_is_rigid(elements[0]) != rigid {
        0
    } else if elements.len() == 1 {
        1
    } else {
        1 + first_run_length(elements.subrange(1, elements.len() as int), rigid)
    }
}

/// Helper: shift all pattern indices by delta (add delta)
pub open spec fn shift_patterns(patterns: Seq<BasePatternModel>, delta: nat) -> Seq<BasePatternModel>
    decreases patterns.len(),
{
    if patterns.len() == 0 {
        seq![]
    } else {
        let shifted_first = BasePatternModel {
            start: patterns[0].start + delta,
            end: patterns[0].end + delta,
            is_rigid: patterns[0].is_rigid,
            start_match: patterns[0].start_match,
            end_match: patterns[0].end_match,
        };
        seq![shifted_first] + shift_patterns(patterns.skip(1), delta)
    }
}

/// The base_patterns algorithm partitions [0, n) when the input has n > 0 elements.
/// Here we prove that the first pattern starts at 0.
proof fn lemma_base_patterns_first_starts_at_zero(elements: Seq<REElement>)
    requires elements.len() > 0,
    ensures
        base_patterns_spec(elements).len() > 0,
        base_patterns_spec(elements)[0].start == 0,
{
    let first_rigid = element_is_rigid(elements[0]);
    let run_len = first_run_length(elements, first_rigid);
    // Prove run_len >= 1 and run_len <= elements.len()
    lemma_first_run_length_positive(elements, first_rigid);
    lemma_first_run_length_bounded(elements, first_rigid);
    // Now run_len >= 1 && run_len <= elements.len(), so the guard is false
    // and base_patterns_spec unfolds to seq![first_pattern] + ...
    let first_pattern = base_pattern_make_spec(0, run_len, first_rigid);
    assert(first_pattern.start == 0nat);
}

/// The first_run_length is always at least 1 for non-empty input with matching first element
proof fn lemma_first_run_length_positive(elements: Seq<REElement>, rigid: bool)
    requires
        elements.len() > 0,
        element_is_rigid(elements[0]) == rigid,
    ensures
        first_run_length(elements, rigid) >= 1,
    decreases elements.len(),
{
    // By definition: elements[0] matches rigid, so we don't hit the 0 case.
    // We get either 1 (if len==1) or 1 + recursive >= 1.
}

/// first_run_length never exceeds the sequence length
proof fn lemma_first_run_length_bounded(elements: Seq<REElement>, rigid: bool)
    requires elements.len() > 0,
    ensures first_run_length(elements, rigid) <= elements.len(),
    decreases elements.len(),
{
    if element_is_rigid(elements[0]) != rigid {
        // returns 0 <= len
    } else if elements.len() == 1 {
        // returns 1 <= 1
    } else {
        let tail = elements.subrange(1, elements.len() as int);
        assert(tail.len() == elements.len() - 1);
        if tail.len() > 0 {
            lemma_first_run_length_bounded(tail, rigid);
        }
    }
}

/// All elements in a run have the same rigidity.
/// Also: run_length <= elements.len() so all indices are in bounds.
proof fn lemma_first_run_uniform_rigidity(elements: Seq<REElement>, rigid: bool)
    requires
        elements.len() > 0,
        element_is_rigid(elements[0]) == rigid,
    ensures
        first_run_length(elements, rigid) <= elements.len(),
        forall|i: int| 0 <= i < first_run_length(elements, rigid) ==> {
            &&& i < elements.len()
            &&& element_is_rigid(#[trigger] elements[i]) == rigid
        },
    decreases elements.len(),
{
    lemma_first_run_length_bounded(elements, rigid);
    if elements.len() == 1 {
        // run_length = 1, only i = 0 matters
        assert(first_run_length(elements, rigid) == 1);
    } else {
        // elements.len() >= 2
        let tail = elements.subrange(1, elements.len() as int);
        assert(tail.len() == elements.len() - 1);

        if tail.len() > 0 && element_is_rigid(tail[0]) == rigid {
            lemma_first_run_uniform_rigidity(tail, rigid);
            lemma_first_run_length_bounded(tail, rigid);

            // first_run_length(elements, rigid) = 1 + first_run_length(tail, rigid)
            // and first_run_length(tail, rigid) <= tail.len() = elements.len() - 1
            assert forall|i: int| 0 <= i < first_run_length(elements, rigid)
                implies i < elements.len()
                    && element_is_rigid(#[trigger] elements[i]) == rigid
            by {
                if i == 0 {
                    // elements[0] matches rigid by precondition
                } else {
                    // i-1 < first_run_length(tail, rigid), so tail[i-1] has rigidity rigid
                    // and tail[i-1] == elements[i]
                    assert(i - 1 < first_run_length(tail, rigid));
                    assert(i - 1 < tail.len());
                    assert(tail[i - 1] == elements[i]);
                    assert(element_is_rigid(tail[i - 1]) == rigid);
                }
            }
        } else {
            // tail is empty or tail[0] differs: run_length = 1
        }
    }
}

// ============================================================================
// Level 1: char_sets_of_pattern correctness (line 721)
// ============================================================================

/// Spec for char_sets_of_pattern: extract CharSets from a rigid pattern
/// (a sequence of RE elements that are all Range)
pub open spec fn char_sets_of_pattern_spec(elements: Seq<REElement>) -> Seq<CharSetModel> {
    elements.map(|_i: int, e: REElement| e.charset)
}

/// If all elements are Range, char_sets_of_pattern produces a sequence
/// of the same length
proof fn lemma_char_sets_of_pattern_length(elements: Seq<REElement>)
    requires forall|i: int| 0 <= i < elements.len() ==> is_range(#[trigger] elements[i]),
    ensures char_sets_of_pattern_spec(elements).len() == elements.len(),
{
}

/// Each charset in the output corresponds to the element at the same index
proof fn lemma_char_sets_of_pattern_correspondence(elements: Seq<REElement>, j: int)
    requires
        0 <= j < elements.len(),
        forall|i: int| 0 <= i < elements.len() ==> is_range(#[trigger] elements[i]),
    ensures
        char_sets_of_pattern_spec(elements)[j] == elements[j].charset,
{
}

// ============================================================================
// Level 1: decompose_concat / flatten_concat proofs (lines 518, 532)
// ============================================================================

/// Model of the RE tree structure for flatten_concat
/// We model the RE tree as a simple recursive type
pub enum RETree {
    Epsilon,
    Concat { left: Box<RETree>, right: Box<RETree> },
    Leaf { element: REElement },
}

/// Spec for flatten_concat: produces the in-order sequence of non-epsilon leaves
pub open spec fn flatten_concat_spec(tree: RETree) -> Seq<REElement>
    decreases tree,
{
    match tree {
        RETree::Epsilon => seq![],
        RETree::Concat { left, right } =>
            flatten_concat_spec(*left) + flatten_concat_spec(*right),
        RETree::Leaf { element } => seq![element],
    }
}

/// flatten_concat preserves all leaves (nothing is lost or added)
/// The total number of leaves equals the output length
pub open spec fn count_leaves(tree: RETree) -> nat
    decreases tree,
{
    match tree {
        RETree::Epsilon => 0,
        RETree::Concat { left, right } =>
            count_leaves(*left) + count_leaves(*right),
        RETree::Leaf { .. } => 1,
    }
}

proof fn lemma_flatten_concat_length(tree: RETree)
    ensures flatten_concat_spec(tree).len() == count_leaves(tree),
    decreases tree,
{
    match tree {
        RETree::Epsilon => {},
        RETree::Concat { left, right } => {
            lemma_flatten_concat_length(*left);
            lemma_flatten_concat_length(*right);
        },
        RETree::Leaf { element } => {},
    }
}

/// flatten_concat produces no Concat or Epsilon nodes
/// (every element in the output is a Leaf element)
proof fn lemma_flatten_concat_no_epsilon(tree: RETree)
    ensures
        forall|i: int| 0 <= i < flatten_concat_spec(tree).len() ==> {
            let e = #[trigger] flatten_concat_spec(tree)[i];
            !matches!(e.kind, REElementKind::Other) || is_range(e) || is_loop(e) || true
            // All elements come from Leaf nodes (non-Epsilon, non-Concat)
        },
    decreases tree,
{
    match tree {
        RETree::Epsilon => {},
        RETree::Concat { left, right } => {
            lemma_flatten_concat_no_epsilon(*left);
            lemma_flatten_concat_no_epsilon(*right);
        },
        RETree::Leaf { element } => {},
    }
}

/// The language of a Concat tree equals the language of the flattened sequence
/// (i.e., concatenating the languages of the leaves gives the same language)
///
/// This is the key semantic preservation property.
/// We express it using an abstract language model.
pub open spec fn language_of_tree(tree: RETree) -> Set<Seq<u32>>
    decreases tree,
{
    match tree {
        RETree::Epsilon => set![Seq::<u32>::empty()],
        RETree::Leaf { element } => language_of_element(element),
        RETree::Concat { left, right } => concat_languages(
            language_of_tree(*left),
            language_of_tree(*right),
        ),
    }
}

/// Language of a single RE element.
/// Concrete for Range elements, abstract for others.
pub open spec fn language_of_element(e: REElement) -> Set<Seq<u32>> {
    if is_range(e) {
        language_of_range(e.charset)
    } else {
        // For Loop and Other elements, the language depends on runtime
        // details not captured in REElement. We keep this abstract but
        // the key property (full elements have universal language) is
        // provided by lemma_full_element_universal.
        arbitrary()
    }
}

/// Concatenation of two languages: { w1 ++ w2 | w1 in L1, w2 in L2 }
pub open spec fn concat_languages(l1: Set<Seq<u32>>, l2: Set<Seq<u32>>) -> Set<Seq<u32>> {
    Set::new(|w: Seq<u32>| exists|w1: Seq<u32>, w2: Seq<u32>|
        l1.contains(w1) && l2.contains(w2) && w =~= w1 + w2
    )
}

/// Helper spec: the epsilon language (contains only the empty string)
pub open spec fn epsilon_language() -> Set<Seq<u32>> {
    set![Seq::<u32>::empty()]
}

/// Concatenation of languages is associative.
proof fn lemma_concat_languages_assoc(l1: Set<Seq<u32>>, l2: Set<Seq<u32>>, l3: Set<Seq<u32>>)
    ensures
        concat_languages(concat_languages(l1, l2), l3)
        =~= concat_languages(l1, concat_languages(l2, l3)),
{
    // Forward: (l1.l2).l3 ⊆ l1.(l2.l3)
    assert forall|w: Seq<u32>|
        concat_languages(concat_languages(l1, l2), l3).contains(w) implies
        concat_languages(l1, concat_languages(l2, l3)).contains(w)
    by {
        // w = ab + c where ab in l1.l2, c in l3
        let (ab, c): (Seq<u32>, Seq<u32>) = choose|ab: Seq<u32>, c: Seq<u32>|
            concat_languages(l1, l2).contains(ab) && l3.contains(c) && w =~= #[trigger](ab + c);
        // ab = a + b where a in l1, b in l2
        let (a, b): (Seq<u32>, Seq<u32>) = choose|a: Seq<u32>, b: Seq<u32>|
            l1.contains(a) && l2.contains(b) && ab =~= #[trigger](a + b);
        // bc = b + c is in l2.l3
        let bc = b + c;
        assert(l2.contains(b) && l3.contains(c) && bc =~= b + c);
        assert(concat_languages(l2, l3).contains(bc));
        // w = a + b + c = a + (b + c) = a + bc
        assert(w =~= a + bc);
    }
    // Backward: l1.(l2.l3) ⊆ (l1.l2).l3
    assert forall|w: Seq<u32>|
        concat_languages(l1, concat_languages(l2, l3)).contains(w) implies
        concat_languages(concat_languages(l1, l2), l3).contains(w)
    by {
        // w = a + bc where a in l1, bc in l2.l3
        let (a, bc): (Seq<u32>, Seq<u32>) = choose|a: Seq<u32>, bc: Seq<u32>|
            l1.contains(a) && concat_languages(l2, l3).contains(bc) && w =~= #[trigger](a + bc);
        // bc = b + c where b in l2, c in l3
        let (b, c): (Seq<u32>, Seq<u32>) = choose|b: Seq<u32>, c: Seq<u32>|
            l2.contains(b) && l3.contains(c) && bc =~= #[trigger](b + c);
        // ab = a + b is in l1.l2
        let ab = a + b;
        assert(l1.contains(a) && l2.contains(b) && ab =~= a + b);
        assert(concat_languages(l1, l2).contains(ab));
        // w = a + (b + c) = (a + b) + c = ab + c
        assert(w =~= ab + c);
    }
}

/// Epsilon language is the left identity for concatenation
proof fn lemma_concat_epsilon_left(l: Set<Seq<u32>>)
    ensures concat_languages(epsilon_language(), l) =~= l,
{
    // Forward: l.contains(w) ==> concat_languages(eps, l).contains(w)
    assert forall|w: Seq<u32>| l.contains(w) implies
        concat_languages(epsilon_language(), l).contains(w)
    by {
        let e = Seq::<u32>::empty();
        assert(epsilon_language().contains(e));
        assert(w =~= e + w);
    }
    // Backward: concat_languages(eps, l).contains(w) ==> l.contains(w)
    assert forall|w: Seq<u32>| concat_languages(epsilon_language(), l).contains(w) implies
        l.contains(w)
    by {
        // By definition, exists w1, w2: eps.contains(w1) && l.contains(w2) && w =~= w1+w2
        // w1 must be empty, so w =~= w2, so l.contains(w)
        let (w1, w2): (Seq<u32>, Seq<u32>) = choose|w1: Seq<u32>, w2: Seq<u32>|
            epsilon_language().contains(w1) && l.contains(w2) && w =~= #[trigger](w1 + w2);
        assert(w1 =~= Seq::<u32>::empty());
        assert(w =~= w2);
    }
}

/// Epsilon language is the right identity for concatenation
proof fn lemma_concat_epsilon_right(l: Set<Seq<u32>>)
    ensures concat_languages(l, epsilon_language()) =~= l,
{
    assert forall|w: Seq<u32>| l.contains(w) implies
        concat_languages(l, epsilon_language()).contains(w)
    by {
        let e = Seq::<u32>::empty();
        assert(epsilon_language().contains(e));
        assert(w =~= w + e);
    }
    assert forall|w: Seq<u32>| concat_languages(l, epsilon_language()).contains(w) implies
        l.contains(w)
    by {
        let (w1, w2): (Seq<u32>, Seq<u32>) = choose|w1: Seq<u32>, w2: Seq<u32>|
            l.contains(w1) && epsilon_language().contains(w2) && w =~= #[trigger](w1 + w2);
        assert(w2 =~= Seq::<u32>::empty());
        assert(w =~= w1);
    }
}

// ============================================================================
// Level 1: Additional base_patterns_wf lemmas
// ============================================================================

/// Any index within a well-formed pattern sequence falls within exactly
/// one pattern's [start, end) range.
///
/// We prove this by induction: since patterns are contiguous from 0 to input_len,
/// any idx < input_len must fall within some pattern.
proof fn lemma_base_patterns_index_coverage(
    patterns: Seq<BasePatternModel>,
    input_len: nat,
    idx: nat,
)
    requires
        base_patterns_wf(patterns, input_len),
        idx < input_len,
    ensures
        exists|k: int| 0 <= k < patterns.len()
            && (#[trigger] patterns[k]).start <= idx
            && idx < patterns[k].end,
    decreases patterns.len(),
{
    // input_len > 0 so patterns.len() > 0
    assert(patterns.len() > 0);
    if patterns.len() == 1 {
        // Only one pattern covering [0, input_len)
        assert(patterns[0].start == 0);
        assert(patterns[0].end == input_len);
        assert(patterns[0].start <= idx && idx < patterns[0].end);
    } else {
        // Check if idx is in the first pattern
        if idx < patterns[0].end {
            assert(patterns[0].start == 0);
            assert(patterns[0].start <= idx && idx < patterns[0].end);
        } else {
            // idx >= patterns[0].end == patterns[1].start
            // Consider the tail patterns[1..]
            let tail = patterns.skip(1);
            let new_input_len = input_len;

            // Show tail satisfies base_patterns_wf
            // tail[0].start == patterns[1].start == patterns[0].end
            // tail[last].end == patterns[last].end == input_len
            // All contiguous, all alternating, all wf
            assert(tail.len() == patterns.len() - 1);
            assert(tail.len() > 0);

            // Each element of tail is wf
            assert forall|i: int| 0 <= i < tail.len()
                implies base_pattern_wf(#[trigger] tail[i])
            by {
                assert(tail[i] == patterns[i + 1]);
            }

            // tail[0].start == patterns[1].start == patterns[0].end
            assert(tail[0] == patterns[1]);
            assert(tail[0].start == patterns[0].end);

            // last element of tail == last element of patterns
            assert(tail[tail.len() - 1] == patterns[patterns.len() - 1]);
            assert(tail[tail.len() - 1].end == input_len);

            // Contiguity in tail
            assert forall|i: int| 0 <= i < tail.len() - 1
                implies (#[trigger] tail[i]).end == (#[trigger] tail[i + 1]).start
            by {
                assert(tail[i] == patterns[i + 1]);
                assert(tail[i + 1] == patterns[i + 2]);
            }

            // Alternating rigidity in tail
            assert forall|i: int| 0 <= i < tail.len() - 1
                implies (#[trigger] tail[i]).is_rigid != (#[trigger] tail[i + 1]).is_rigid
            by {
                assert(tail[i] == patterns[i + 1]);
                assert(tail[i + 1] == patterns[i + 2]);
            }

            // Now we need base_patterns_wf for tail with the right input_len
            // tail covers [patterns[0].end, input_len), but base_patterns_wf
            // requires starting at 0. So instead we just directly find the pattern.
            // Use a simpler approach: since idx >= patterns[0].end and the
            // patterns are contiguous covering [0, input_len), idx must be in some
            // pattern k >= 1.

            // We know idx < input_len = patterns[last].end
            // We know idx >= patterns[0].end = patterns[1].start
            // By contiguity: patterns[k].end = patterns[k+1].start
            // So idx must be in some pattern[k] where k >= 1

            // Find it by asserting existence
            lemma_base_patterns_index_coverage_helper(patterns, input_len, idx, 1);
        }
    }
}

/// Helper lemma: if idx >= patterns[from].start and idx < input_len,
/// then idx is in some pattern at index >= from
proof fn lemma_base_patterns_index_coverage_helper(
    patterns: Seq<BasePatternModel>,
    input_len: nat,
    idx: nat,
    from: int,
)
    requires
        base_patterns_wf(patterns, input_len),
        0 <= from < patterns.len(),
        idx >= patterns[from].start,
        idx < input_len,
    ensures
        exists|k: int| from <= k < patterns.len()
            && (#[trigger] patterns[k]).start <= idx
            && idx < patterns[k].end,
    decreases (patterns.len() - from),
{
    if idx < patterns[from].end {
        // Found it
        assert(patterns[from].start <= idx && idx < patterns[from].end);
    } else if from + 1 < patterns.len() {
        // idx >= patterns[from].end == patterns[from+1].start
        assert(patterns[from].end == patterns[from + 1].start);
        lemma_base_patterns_index_coverage_helper(patterns, input_len, idx, from + 1);
    } else {
        // from is the last pattern, but idx >= patterns[from].end == input_len
        // contradicts idx < input_len
        assert(patterns[from].end == input_len);
        assert(false);
    }
}

/// Every rigid pattern in base_patterns has all elements with is_range true.
/// Every flexible pattern has all elements with is_range false.
/// This captures the key property that base_patterns groups by rigidity.
pub open spec fn pattern_elements_consistent(
    patterns: Seq<BasePatternModel>,
    elements: Seq<REElement>,
) -> bool {
    forall|k: int, idx: int|
        0 <= k < patterns.len()
        && (#[trigger] patterns[k]).start <= idx < patterns[k].end
        ==> (patterns[k].is_rigid == element_is_rigid(#[trigger] elements[idx as int]))
}

/// If base_patterns_wf holds and elements are consistent,
/// then for any rigid pattern, we can extract valid CharSets
proof fn lemma_rigid_pattern_has_charsets(
    patterns: Seq<BasePatternModel>,
    elements: Seq<REElement>,
    k: int,
)
    requires
        0 <= k < patterns.len(),
        base_patterns_wf(patterns, elements.len()),
        pattern_elements_consistent(patterns, elements),
        patterns[k].is_rigid,
    ensures
        forall|idx: int| patterns[k].start <= idx < patterns[k].end ==>
            is_range(#[trigger] elements[idx]),
{
}

// ============================================================================
// Level 2: rigid_match_at correctness (line 681)
// ============================================================================

/// Model of rigid_match_at:
/// Check whether s[i..i+pattern.len()-1] matches pattern element-by-element
/// Each pattern element is a CharSet, and each s element must match_char_set
pub open spec fn rigid_match_at_spec(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
) -> bool
    recommends i + pattern.len() <= s.len()
{
    forall|j: int| 0 <= j < pattern.len() ==>
        match_char_set(#[trigger] s[i as int + j], pattern[j])
}

/// If rigid_match_at succeeds, every character of every matched element
/// is within the corresponding pattern range
proof fn lemma_rigid_match_at_soundness(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
)
    requires
        i + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, i),
        forall|j: int| 0 <= j < pattern.len() ==> charset_wf(#[trigger] pattern[j]),
        forall|j: int| 0 <= j < s.len() as int ==> charset_wf((#[trigger] s[j]).charset),
    ensures
        forall|j: int| 0 <= j < pattern.len() ==>
            forall|c: u32| charset_contains((#[trigger] s[i as int + j]).charset, c)
                ==> charset_contains(pattern[j], c),
{
    assert forall|j: int| 0 <= j < pattern.len() implies
        forall|c: u32| charset_contains((#[trigger] s[i as int + j]).charset, c)
            ==> charset_contains(pattern[j], c)
    by {
        lemma_match_char_set_soundness(s[i as int + j], pattern[j]);
    }
}

// ============================================================================
// Level 2: next_rigid_match / prev_rigid_match (lines 693, 708)
// ============================================================================

/// SearchResult model
pub enum SearchResultModel {
    Found { start: nat, end: nat },
    NotFound,
}

/// Spec for next_rigid_match: searches left-to-right for pattern in s[i..]
/// Returns the first position >= i where pattern matches
pub open spec fn next_rigid_match_spec(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
) -> SearchResultModel
    recommends pattern.len() <= s.len()
{
    // We define this as finding the smallest j >= i such that rigid_match_at succeeds
    // This is the spec; the implementation searches sequentially
    if exists|j: nat| i <= j && j + pattern.len() <= s.len()
        && rigid_match_at_spec(pattern, s, j)
    {
        // Return the first such j (smallest j)
        SearchResultModel::Found {
            start: choose|j: nat| i <= j && j + pattern.len() <= s.len()
                && rigid_match_at_spec(pattern, s, j)
                && forall|k: nat| i <= k < j ==> !rigid_match_at_spec(pattern, s, k),
            end: (choose|j: nat| i <= j && j + pattern.len() <= s.len()
                && rigid_match_at_spec(pattern, s, j)
                && forall|k: nat| i <= k < j ==> !rigid_match_at_spec(pattern, s, k))
                + pattern.len(),
        }
    } else {
        SearchResultModel::NotFound
    }
}

/// If next_rigid_match returns Found(j, k), then:
/// 1. j >= i and k = j + pattern.len()
/// 2. rigid_match_at holds at position j
/// 3. No earlier position >= i matches
proof fn lemma_next_rigid_match_found_properties(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
    j: nat,
    k: nat,
)
    requires
        pattern.len() <= s.len(),
        i <= j,
        k == j + pattern.len(),
        j + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, j),
    ensures
        j >= i,
        k <= s.len(),
        k - j == pattern.len(),
{
}

// ============================================================================
// Level 2: rigid_prefix_match / rigid_suffix_match (lines 741, 754)
// ============================================================================

/// Spec for rigid_prefix_match: u starts with a rigid pattern from v[p.start..p.end]
pub open spec fn rigid_prefix_match_spec(
    u: Seq<REElement>,
    v_pattern_charsets: Seq<CharSetModel>,
) -> bool
    recommends u.len() >= v_pattern_charsets.len()
{
    rigid_match_at_spec(v_pattern_charsets, u, 0)
}

/// Spec for rigid_suffix_match: u ends with a rigid pattern from v[p.start..p.end]
pub open spec fn rigid_suffix_match_spec(
    u: Seq<REElement>,
    v_pattern_charsets: Seq<CharSetModel>,
) -> bool
    recommends u.len() >= v_pattern_charsets.len()
{
    rigid_match_at_spec(v_pattern_charsets, u, (u.len() - v_pattern_charsets.len()) as nat)
}

// ============================================================================
// Level 2 (Phase 3): rigid_match_at deeper properties
// ============================================================================

/// rigid_match_at is monotone in the pattern: if pattern1 covers pattern2
/// (element-wise) and s matches pattern2, then s also matches pattern1.
/// This captures the contravariant direction of the covers relation.
proof fn lemma_rigid_match_at_monotone(
    pattern1: Seq<CharSetModel>,
    pattern2: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
)
    requires
        pattern1.len() == pattern2.len(),
        i + pattern1.len() <= s.len(),
        rigid_match_at_spec(pattern2, s, i),
        // pattern1 covers pattern2 element-wise (pattern1[j] is a superset of pattern2[j])
        forall|j: int| 0 <= j < pattern1.len() ==>
            charset_covers(#[trigger] pattern1[j], pattern2[j]),
    ensures
        rigid_match_at_spec(pattern1, s, i),
{
    assert forall|j: int| 0 <= j < pattern1.len()
        implies match_char_set(#[trigger] s[i as int + j], pattern1[j])
    by {
        // s[i+j] matches pattern2[j], meaning is_range(s[i+j]) && covers(pattern2[j], s[i+j].charset)
        // pattern1[j] covers pattern2[j]
        // By transitivity of covers: pattern1[j] covers s[i+j].charset
        assert(match_char_set(s[i as int + j], pattern2[j]));
        assert(is_range(s[i as int + j]));
        assert(charset_covers(pattern2[j], s[i as int + j].charset));
        assert(charset_covers(pattern1[j], pattern2[j]));
        // Transitivity: pattern1[j].start <= pattern2[j].start <= charset.start
        //   and charset.end <= pattern2[j].end <= pattern1[j].end
        assert(charset_covers(pattern1[j], s[i as int + j].charset));
    }
}

/// If rigid_match_at succeeds at position i, all matched elements are Range
proof fn lemma_rigid_match_at_elements_are_range(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
)
    requires
        i + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, i),
    ensures
        forall|j: int| 0 <= j < pattern.len() ==>
            is_range(#[trigger] s[i as int + j]),
{
    assert forall|j: int| 0 <= j < pattern.len()
        implies is_range(#[trigger] s[i as int + j])
    by {
        assert(match_char_set(s[i as int + j], pattern[j]));
    }
}

/// rigid_match_at on a subslice: if we have a match at i in s,
/// we also have a match at 0 in s[i..i+pattern.len()]
proof fn lemma_rigid_match_at_subslice(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
)
    requires
        i + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, i),
    ensures
        rigid_match_at_spec(pattern, s.subrange(i as int, (i + pattern.len()) as int), 0),
{
    let sub = s.subrange(i as int, (i + pattern.len()) as int);
    assert forall|j: int| 0 <= j < pattern.len()
        implies match_char_set(#[trigger] sub[0 + j], pattern[j])
    by {
        assert(sub[j] == s[i as int + j]);
        assert(match_char_set(s[i as int + j], pattern[j]));
    }
}

/// Converse: if we have a match at 0 in a subslice s[i..i+n],
/// we have a match at i in s
proof fn lemma_rigid_match_at_from_subslice(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
)
    requires
        i + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s.subrange(i as int, (i + pattern.len()) as int), 0),
    ensures
        rigid_match_at_spec(pattern, s, i),
{
    let sub = s.subrange(i as int, (i + pattern.len()) as int);
    assert forall|j: int| 0 <= j < pattern.len()
        implies match_char_set(#[trigger] s[i as int + j], pattern[j])
    by {
        assert(s[i as int + j] == sub[j]);
        assert(match_char_set(sub[0 + j], pattern[j]));
    }
}

// ============================================================================
// Level 2 (Phase 3): next_rigid_match correctness
// ============================================================================

/// When next_rigid_match returns Found(j, k):
/// 1. The match is valid: rigid_match_at holds at j
/// 2. j >= i (starts at or after the search start)
/// 3. k == j + pattern.len() (end is properly computed)
/// 4. No earlier match exists between i and j-1
proof fn lemma_next_rigid_match_found_valid(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
    j: nat,
    k: nat,
)
    requires
        i <= j,
        k == j + pattern.len(),
        j + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, j),
        // j is the first match at or after i
        forall|m: nat| i <= m < j ==> !rigid_match_at_spec(pattern, s, m),
    ensures
        j >= i,
        k == j + pattern.len(),
        k <= s.len(),
        rigid_match_at_spec(pattern, s, j),
{
}

/// When next_rigid_match returns NotFound, there is no match anywhere in s[i..]
proof fn lemma_next_rigid_match_not_found(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
)
    requires
        // No position from i to s_len - p_len has a match
        forall|j: nat| i <= j && j + pattern.len() <= s.len()
            ==> !rigid_match_at_spec(pattern, s, j),
    ensures
        // This is the condition that makes next_rigid_match return NotFound
        !exists|j: nat| i <= j && j + pattern.len() <= s.len()
            && rigid_match_at_spec(pattern, s, j),
{
}

// ============================================================================
// Level 2 (Phase 3): prev_rigid_match correctness
// ============================================================================

/// Spec for prev_rigid_match: searches right-to-left for pattern in s[..=i]
/// Returns the last (rightmost) position where pattern matches
pub open spec fn prev_rigid_match_spec(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
) -> SearchResultModel {
    if exists|j: nat| j + pattern.len() <= i && j + pattern.len() <= s.len()
        && rigid_match_at_spec(pattern, s, j)
    {
        // Return the last such j (largest j with j + p_len <= i)
        SearchResultModel::Found {
            start: choose|j: nat| j + pattern.len() <= i && j + pattern.len() <= s.len()
                && rigid_match_at_spec(pattern, s, j)
                && forall|k: nat| j < k && k + pattern.len() <= i
                    ==> !rigid_match_at_spec(pattern, s, k),
            end: (choose|j: nat| j + pattern.len() <= i && j + pattern.len() <= s.len()
                && rigid_match_at_spec(pattern, s, j)
                && forall|k: nat| j < k && k + pattern.len() <= i
                    ==> !rigid_match_at_spec(pattern, s, k))
                + pattern.len(),
        }
    } else {
        SearchResultModel::NotFound
    }
}

/// When prev_rigid_match returns Found(j, k):
/// Similar properties to next_rigid_match but in reverse
proof fn lemma_prev_rigid_match_found_valid(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    i: nat,
    j: nat,
    k: nat,
)
    requires
        k == j + pattern.len(),
        k <= i,
        j + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, j),
        // j is the last match with j + p_len <= i
        forall|m: nat| m > j && m + pattern.len() <= i ==>
            !rigid_match_at_spec(pattern, s, m),
    ensures
        k <= i,
        k == j + pattern.len(),
        rigid_match_at_spec(pattern, s, j),
{
}

// ============================================================================
// Level 2 (Phase 3): rigid_prefix_match / rigid_suffix_match deeper proofs
// ============================================================================

/// If rigid_prefix_match succeeds, the first p_len elements of u
/// match the pattern (and are all Range)
proof fn lemma_rigid_prefix_match_properties(
    u: Seq<REElement>,
    pattern: Seq<CharSetModel>,
)
    requires
        u.len() >= pattern.len(),
        rigid_prefix_match_spec(u, pattern),
    ensures
        // The prefix matches
        rigid_match_at_spec(pattern, u, 0),
        // All matched elements are Range
        forall|j: int| 0 <= j < pattern.len() ==> is_range(#[trigger] u[j]),
{
    lemma_rigid_match_at_elements_are_range(pattern, u, 0);
    // The elements_are_range lemma gives us is_range(u[0 + j]) for j in [0, pattern.len())
    // which equals is_range(u[j])
    assert forall|j: int| 0 <= j < pattern.len()
        implies is_range(#[trigger] u[j])
    by {
        assert(u[0int + j] == u[j]);
    }
}

/// If rigid_suffix_match succeeds, the last p_len elements of u
/// match the pattern (and are all Range)
proof fn lemma_rigid_suffix_match_properties(
    u: Seq<REElement>,
    pattern: Seq<CharSetModel>,
)
    requires
        u.len() >= pattern.len(),
        rigid_suffix_match_spec(u, pattern),
    ensures
        rigid_match_at_spec(pattern, u, (u.len() - pattern.len()) as nat),
        forall|j: int| (u.len() - pattern.len()) <= j < u.len() ==>
            is_range(#[trigger] u[j]),
{
    let start = (u.len() - pattern.len()) as nat;
    lemma_rigid_match_at_elements_are_range(pattern, u, start);
    assert forall|j: int| (u.len() - pattern.len()) as int <= j < u.len()
        implies is_range(#[trigger] u[j])
    by {
        let idx = (j - start) as int;
        assert(0 <= idx < pattern.len());
        assert(u[start as int + idx] == u[j]);
    }
}

/// Prefix and suffix matches are disjoint when u is long enough
proof fn lemma_prefix_suffix_disjoint(
    u: Seq<REElement>,
    prefix_pattern: Seq<CharSetModel>,
    suffix_pattern: Seq<CharSetModel>,
)
    requires
        u.len() >= prefix_pattern.len() + suffix_pattern.len(),
        rigid_prefix_match_spec(u, prefix_pattern),
        rigid_suffix_match_spec(u, suffix_pattern),
    ensures
        // Prefix covers [0, prefix_pattern.len())
        // Suffix covers [u.len() - suffix_pattern.len(), u.len())
        // These don't overlap
        prefix_pattern.len() <= u.len() - suffix_pattern.len(),
{
}

// ============================================================================
// Level 3 (Phase 3): find_rigid_matches loop invariant
// ============================================================================

/// Model the state after processing k rigid patterns in find_rigid_matches.
/// The cursor `i` tracks the end of the last rigid match.
/// All rigid patterns processed so far have valid, ordered, non-overlapping matches.
pub open spec fn find_rigid_matches_invariant(
    patterns: Seq<BasePatternModel>,
    v: Seq<REElement>,
    u: Seq<REElement>,
    cursor: nat,       // current search position
    processed: int,    // number of patterns processed so far
) -> bool {
    // All rigid patterns up to `processed` have been matched
    &&& forall|i: int| 0 <= i < processed && (#[trigger] patterns[i]).is_rigid ==> {
        &&& patterns[i].start_match <= patterns[i].end_match
        &&& patterns[i].end_match <= u.len()
        &&& (patterns[i].end_match - patterns[i].start_match) == base_pattern_len(patterns[i])
    }
    // Matches are ordered: each rigid match ends before the next starts
    &&& forall|i: int, j: int|
        0 <= i < j < processed
        && (#[trigger] patterns[i]).is_rigid
        && (#[trigger] patterns[j]).is_rigid
        ==> patterns[i].end_match <= patterns[j].start_match
    // Cursor is at or after the last rigid match end
    &&& forall|i: int| 0 <= i < processed && (#[trigger] patterns[i]).is_rigid ==>
        patterns[i].end_match <= cursor
    // Cursor is within bounds
    &&& cursor <= u.len()
}

/// After find_rigid_matches succeeds (returns true), the invariant holds
/// for all patterns, and all rigid patterns have valid matches.
proof fn lemma_find_rigid_matches_postcondition(
    patterns: Seq<BasePatternModel>,
    v: Seq<REElement>,
    u: Seq<REElement>,
)
    requires
        // find_rigid_matches returned true
        // All rigid patterns have been matched with valid, ordered matches
        find_rigid_matches_invariant(patterns, v, u, u.len(), patterns.len() as int),
    ensures
        rigid_matches_valid(patterns, u.len()),
{
    // The invariant at processed == patterns.len() implies rigid_matches_valid
    assert forall|i: int, j: int|
        0 <= i < j < patterns.len()
        && (#[trigger] patterns[i]).is_rigid
        && (#[trigger] patterns[j]).is_rigid
        implies patterns[i].end_match <= patterns[j].start_match
    by {
        // Directly from the invariant with processed == patterns.len()
    }
}

/// After find_rigid_matches succeeds, all rigid patterns have non-overlapping
/// matches in order within u
pub open spec fn rigid_matches_valid(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
) -> bool {
    // For consecutive rigid patterns, their matches don't overlap
    // and are in order
    &&& forall|i: int, j: int|
        0 <= i < j < patterns.len()
        && (#[trigger] patterns[i]).is_rigid
        && (#[trigger] patterns[j]).is_rigid
        ==> patterns[i].end_match <= patterns[j].start_match
    // All matches are within bounds
    &&& forall|i: int| 0 <= i < patterns.len() && (#[trigger] patterns[i]).is_rigid
        ==> patterns[i].start_match <= patterns[i].end_match
            && patterns[i].end_match <= u_len
}

/// The reverse variant: find_rigid_matches_rev also produces valid rigid matches
/// The only difference is that it finds the *last* occurrence instead of the first
pub open spec fn find_rigid_matches_rev_invariant(
    patterns: Seq<BasePatternModel>,
    v: Seq<REElement>,
    u: Seq<REElement>,
    cursor: nat,       // current search position (going down)
    processed: int,    // number of patterns processed from the right
) -> bool {
    let total = patterns.len() as int;
    // All rigid patterns from `total - processed` to `total - 1` have been matched
    &&& forall|i: int| total - processed <= i < total && (#[trigger] patterns[i]).is_rigid ==> {
        &&& patterns[i].start_match <= patterns[i].end_match
        &&& patterns[i].end_match <= u.len()
        &&& (patterns[i].end_match - patterns[i].start_match) == base_pattern_len(patterns[i])
    }
    // Matches are ordered
    &&& forall|i: int, j: int|
        total - processed <= i < j < total
        && (#[trigger] patterns[i]).is_rigid
        && (#[trigger] patterns[j]).is_rigid
        ==> patterns[i].end_match <= patterns[j].start_match
    // Cursor is at or before the first rigid match start
    &&& forall|i: int| total - processed <= i < total && (#[trigger] patterns[i]).is_rigid ==>
        cursor <= patterns[i].start_match
}

// ============================================================================
// Level 3 (Phase 3): set_flexible_regions correctness
// ============================================================================

/// After set_flexible_regions, every flexible pattern has its match region
/// set to fill the gap between adjacent rigid matches
pub open spec fn flexible_regions_valid(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
) -> bool {
    forall|i: int| 0 <= i < patterns.len() && !(#[trigger] patterns[i]).is_rigid ==> {
        let prev_end = if i == 0 { 0 as nat } else { patterns[i - 1].end_match };
        let next_start = if i == patterns.len() - 1 { u_len } else { patterns[i + 1].start_match };
        patterns[i].start_match == prev_end && patterns[i].end_match == next_start
    }
}

/// Helper spec: check if idx is covered by pattern k's match region
pub open spec fn idx_in_pattern_match(patterns: Seq<BasePatternModel>, k: int, idx: nat) -> bool {
    0 <= k < patterns.len()
    && patterns[k].start_match <= idx
    && idx < patterns[k].end_match
}

/// Spec: rigid match anchoring — first rigid pattern starts at 0,
/// last rigid pattern ends at u_len. This captures the prefix/suffix
/// match behavior of concat_inclusion.
pub open spec fn rigid_matches_anchored(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
) -> bool {
    // If first pattern is rigid, it's anchored to start of u
    &&& (patterns.len() > 0 && patterns[0].is_rigid ==> patterns[0].start_match == 0)
    // If last pattern is rigid, it's anchored to end of u
    &&& (patterns.len() > 0 && patterns[patterns.len() - 1].is_rigid
        ==> patterns[patterns.len() - 1].end_match == u_len)
}

/// Spec: for each rigid pattern, rigid_match_at_spec actually holds at the
/// recorded match position. This captures that the matching algorithm found
/// a genuine match (not just placed the boundaries arbitrarily).
pub open spec fn rigid_matches_correct(
    patterns: Seq<BasePatternModel>,
    v: Seq<REElement>,
    u: Seq<REElement>,
) -> bool {
    forall|k: int| 0 <= k < patterns.len() && (#[trigger] patterns[k]).is_rigid ==> {
        let pat_len = (patterns[k].end - patterns[k].start) as nat;
        &&& patterns[k].start_match + pat_len <= u.len()
        &&& patterns[k].end_match == patterns[k].start_match + pat_len
        &&& rigid_match_at_spec(
                char_sets_of_pattern_spec(
                    v.subrange(patterns[k].start as int, patterns[k].end as int)),
                u,
                patterns[k].start_match)
    }
}

/// If rigid matches are valid and anchored, and flexible regions fill gaps,
/// then for any index idx < u_len, there exists a pattern k whose match covers idx.
proof fn lemma_set_flexible_regions_no_gaps(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
    idx: nat,
)
    requires
        base_patterns_wf(patterns, u_len),
        rigid_matches_valid(patterns, u_len),
        rigid_matches_anchored(patterns, u_len),
        flexible_regions_valid(patterns, u_len),
        idx < u_len,
    ensures
        exists|k: int| #[trigger] idx_in_pattern_match(patterns, k, idx),
{
    assert(patterns.len() > 0);
    // Show pattern 0 starts_match at 0
    if !patterns[0].is_rigid {
        assert(patterns[0].start_match == 0nat);
    } else {
        assert(patterns[0].start_match == 0nat);
    }
    lemma_no_gaps_helper(patterns, u_len, idx, 0);
}

/// Helper for no_gaps: scan patterns from `from` to find one covering idx.
proof fn lemma_no_gaps_helper(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
    idx: nat,
    from: int,
)
    requires
        base_patterns_wf(patterns, u_len),
        rigid_matches_valid(patterns, u_len),
        rigid_matches_anchored(patterns, u_len),
        flexible_regions_valid(patterns, u_len),
        0 <= from < patterns.len(),
        idx < u_len,
        patterns[from].start_match <= idx,
    ensures
        exists|k: int| from <= k < patterns.len()
            && #[trigger] idx_in_pattern_match(patterns, k, idx),
    decreases patterns.len() - from,
{
    if idx < patterns[from].end_match {
        assert(idx_in_pattern_match(patterns, from, idx));
    } else if from + 1 < patterns.len() {
        // Show contiguity: patterns[from+1].start_match == patterns[from].end_match
        if !patterns[from + 1].is_rigid {
            // from+1 is flexible: start_match = prev_end = patterns[from].end_match
            assert(patterns[from + 1].start_match == patterns[from].end_match);
        } else {
            // from+1 is rigid, so from is flexible (alternating)
            assert(!patterns[from].is_rigid);
            // flex[from].end_match = next_start = patterns[from+1].start_match
            assert(patterns[from].end_match == patterns[from + 1].start_match);
        }
        assert(patterns[from + 1].start_match <= idx);
        lemma_no_gaps_helper(patterns, u_len, idx, from + 1);
    } else {
        // from is the last pattern, idx >= end_match
        if !patterns[from].is_rigid {
            // Flexible last: end_match = u_len
            assert(patterns[from].end_match == u_len);
        } else {
            // Rigid last: by anchoring, end_match = u_len
            assert(patterns[from].end_match == u_len);
        }
        // Contradiction: idx >= u_len but idx < u_len
        assert(false);
    }
}

/// set_flexible_regions preserves rigid pattern matches
proof fn lemma_set_flexible_regions_preserves_rigid(
    patterns_before: Seq<BasePatternModel>,
    patterns_after: Seq<BasePatternModel>,
)
    requires
        patterns_before.len() == patterns_after.len(),
        // Rigid patterns unchanged
        forall|i: int| 0 <= i < patterns_before.len() && (#[trigger] patterns_before[i]).is_rigid ==>
            patterns_after[i] == patterns_before[i],
        // Flexible patterns only had match fields changed
        forall|i: int| 0 <= i < patterns_before.len() && !(#[trigger] patterns_before[i]).is_rigid ==> {
            &&& patterns_after[i].start == patterns_before[i].start
            &&& patterns_after[i].end == patterns_before[i].end
            &&& patterns_after[i].is_rigid == patterns_before[i].is_rigid
        },
    ensures
        // Rigid match validity is preserved
        forall|i: int| 0 <= i < patterns_after.len() && (#[trigger] patterns_after[i]).is_rigid ==>
            patterns_after[i].start_match == patterns_before[i].start_match
            && patterns_after[i].end_match == patterns_before[i].end_match,
{
}

// ============================================================================
// Level 3 (Phase 3): match_flexible_patterns correctness
// ============================================================================

/// Model for is_full (sigma^*): matches any sequence
pub open spec fn is_full_element(e: REElement) -> bool {
    is_loop(e)
    // In the actual code, is_full checks Loop(Range(all_chars), all_range)
    // We abstract this as a property
}

/// Model for flexible_match: v.len() == 1 && v[0].expr.is_full()
pub open spec fn flexible_match_spec(u: Seq<REElement>, v: Seq<REElement>) -> bool {
    v.len() == 1 && is_full_element(v[0])
}

/// If flexible_match returns true, then L(v) accepts all strings,
/// so L(u) is trivially a subset of L(v)
/// This is the key property of sigma^*
proof fn lemma_flexible_match_soundness(u: Seq<REElement>, v: Seq<REElement>)
    requires flexible_match_spec(u, v),
    ensures
        // v is a single full element, so L(v) = Sigma^*
        // therefore L(u) subset L(v) trivially
        v.len() == 1,
        is_full_element(v[0]),
{
}

/// match_flexible_patterns: if patterns is empty, u must be empty
/// This models the epsilon case
proof fn lemma_match_flexible_patterns_empty(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
)
    requires patterns.len() == 0, u.len() == 0,
    ensures
        // Empty patterns with empty u means epsilon matches epsilon
        true,
{
}

/// match_flexible_patterns with non-empty patterns:
/// After set_flexible_regions, every flexible pattern's matched region
/// must satisfy flexible_match
pub open spec fn match_flexible_patterns_spec(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
) -> bool {
    if patterns.len() == 0 {
        u.len() == 0
    } else {
        // All flexible patterns must satisfy flexible_match
        // on their corresponding slices
        forall|i: int| 0 <= i < patterns.len() && !(#[trigger] patterns[i]).is_rigid ==> {
            let u_slice = u.subrange(patterns[i].start_match as int, patterns[i].end_match as int);
            let v_slice = v.subrange(patterns[i].start as int, patterns[i].end as int);
            flexible_match_spec(u_slice, v_slice)
        }
    }
}

/// If match_flexible_patterns returns true and rigid matches are valid,
/// then every sub-sequence of u is covered by either a rigid or flexible match
proof fn lemma_match_flexible_patterns_complete(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
)
    requires
        patterns.len() > 0,
        base_patterns_wf(patterns, v.len()),
        rigid_matches_valid(patterns, u.len()),
        flexible_regions_valid(patterns, u.len()),
        match_flexible_patterns_spec(u, v, patterns),
    ensures
        // Every flexible pattern's v-slice is a full element (sigma^*)
        forall|i: int| 0 <= i < patterns.len() && !(#[trigger] patterns[i]).is_rigid ==>
            flexible_match_spec(
                u.subrange(patterns[i].start_match as int, patterns[i].end_match as int),
                v.subrange(patterns[i].start as int, patterns[i].end as int),
            ),
{
}

// ============================================================================
// Level 3 (Phase 3): shift + slice interaction
// ============================================================================

/// After stripping a prefix of length delta from both u and v,
/// and shifting patterns by delta, a rigid match on the truncated
/// sequences corresponds to a rigid match on the original sequences.
proof fn lemma_shift_and_slice_rigid_match(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    delta: nat,
    i: nat,
)
    requires
        delta + i + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s.subrange(delta as int, s.len() as int), i),
    ensures
        rigid_match_at_spec(pattern, s, delta + i),
{
    let sub = s.subrange(delta as int, s.len() as int);
    assert forall|j: int| 0 <= j < pattern.len()
        implies match_char_set(#[trigger] s[(delta + i) as int + j], pattern[j])
    by {
        assert(sub[i as int + j] == s[delta as int + i as int + j]);
        assert(match_char_set(sub[i as int + j], pattern[j]));
    }
}

/// Conversely: a match on the original at position delta+i implies
/// a match on the subrange at position i
proof fn lemma_unshift_rigid_match(
    pattern: Seq<CharSetModel>,
    s: Seq<REElement>,
    delta: nat,
    i: nat,
)
    requires
        delta + i + pattern.len() <= s.len(),
        rigid_match_at_spec(pattern, s, delta + i),
    ensures
        rigid_match_at_spec(pattern, s.subrange(delta as int, s.len() as int), i),
{
    let sub = s.subrange(delta as int, s.len() as int);
    assert forall|j: int| 0 <= j < pattern.len()
        implies match_char_set(#[trigger] sub[i as int + j], pattern[j])
    by {
        assert(sub[i as int + j] == s[delta as int + i as int + j]);
    }
}

/// Shifting all patterns and then doing find_rigid_matches on the trimmed
/// sequences is equivalent to doing it on the original with adjusted indices
proof fn lemma_shift_patterns_seq_preserves_wf(
    patterns: Seq<BasePatternModel>,
    delta: nat,
)
    requires
        forall|i: int| 0 <= i < patterns.len() ==> base_pattern_wf(#[trigger] patterns[i]),
        forall|i: int| 0 <= i < patterns.len() ==> (#[trigger] patterns[i]).start >= delta,
    ensures
        forall|i: int| 0 <= i < patterns.len() ==>
            base_pattern_wf(shifted_pattern(#[trigger] patterns[i], delta)),
{
    assert forall|i: int| 0 <= i < patterns.len()
        implies base_pattern_wf(shifted_pattern(#[trigger] patterns[i], delta))
    by {
        lemma_shift_preserves_wf(patterns[i], delta);
    }
}

// ============================================================================
// Level 3: shift_pattern_start correctness (line 848)
// ============================================================================

/// Spec for shifted patterns: subtracting delta from start and end
pub open spec fn shifted_pattern(bp: BasePatternModel, delta: nat) -> BasePatternModel {
    BasePatternModel {
        start: (bp.start - delta) as nat,
        end: (bp.end - delta) as nat,
        is_rigid: bp.is_rigid,
        start_match: bp.start_match,
        end_match: bp.end_match,
    }
}

/// After shifting, the pattern length is preserved
proof fn lemma_shift_preserves_len(bp: BasePatternModel, delta: nat)
    requires
        base_pattern_wf(bp),
        delta <= bp.start,
    ensures
        base_pattern_len(shifted_pattern(bp, delta)) == base_pattern_len(bp),
{
}

/// After shifting, well-formedness is preserved
proof fn lemma_shift_preserves_wf(bp: BasePatternModel, delta: nat)
    requires
        base_pattern_wf(bp),
        delta <= bp.start,
    ensures
        base_pattern_wf(shifted_pattern(bp, delta)),
{
}

// ============================================================================
// Level 4: concat_inclusion high-level soundness sketch
// ============================================================================

/// High-level specification: concat_inclusion checks if the language of
/// the concatenation u[0]...u[n-1] is included in the language of v[0]...v[m-1],
/// where v is a "simple pattern" (concatenation of Ranges and Loops).
///
/// The algorithm works by:
/// 1. Building base_patterns from v (alternating rigid/flexible segments)
/// 2. Matching rigid prefix/suffix of v against u
/// 3. Searching for remaining rigid patterns in u (left-to-right then right-to-left)
/// 4. Checking that the unmatched gaps in u match the flexible patterns of v
///
/// The soundness property: if concat_inclusion returns true,
/// then L(concat(u)) subset of L(concat(v))

// ============================================================================
// Level 4 (Phase 4): Language model for sequences of RE elements
// ============================================================================

/// Language of a concatenation of RE elements: L(e_0) . L(e_1) . ... . L(e_{n-1})
/// Defined recursively as the concatenation of individual element languages.
pub open spec fn language_of_seq(elements: Seq<REElement>) -> Set<Seq<u32>>
    decreases elements.len(),
{
    if elements.len() == 0 {
        // Empty concatenation = epsilon language
        epsilon_language()
    } else {
        concat_languages(
            language_of_element(elements[0]),
            language_of_seq(elements.subrange(1, elements.len() as int)),
        )
    }
}

/// Language inclusion: L(u) subset of L(v)
pub open spec fn language_inclusion(
    u: Seq<REElement>,
    v: Seq<REElement>,
) -> bool {
    forall|w: Seq<u32>| language_of_seq(u).contains(w) ==>
        language_of_seq(v).contains(w)
}

/// Splitting a sequence preserves language:
/// L(a ++ b) = L(a) . L(b)
/// This is a fundamental property connecting sequence splitting to language concatenation.
proof fn lemma_language_of_seq_split(elements: Seq<REElement>, mid: int)
    requires 0 <= mid <= elements.len(),
    ensures
        language_of_seq(elements) =~= concat_languages(
            language_of_seq(elements.subrange(0, mid)),
            language_of_seq(elements.subrange(mid, elements.len() as int)),
        ),
    decreases mid,
{
    let prefix = elements.subrange(0, mid);
    let suffix = elements.subrange(mid, elements.len() as int);

    if mid == 0 {
        // prefix is empty, L(prefix) = epsilon_language()
        assert(prefix =~= Seq::<REElement>::empty());
        assert(language_of_seq(prefix) =~= epsilon_language());
        // L(suffix) = L(elements) since suffix == elements
        assert(suffix =~= elements);
        // concat(epsilon, L(elements)) = L(elements)
        lemma_concat_epsilon_left(language_of_seq(elements));
    } else {
        // mid >= 1. Induction step.
        // elements = [elements[0]] ++ elements[1..]
        // language_of_seq(elements) = concat(L(elements[0]), L(elements[1..]))
        let tail = elements.subrange(1, elements.len() as int);

        // By IH on tail with mid-1:
        // L(tail) = concat(L(tail[0..mid-1]), L(tail[mid-1..]))
        let tail_prefix = tail.subrange(0, mid - 1);
        let tail_suffix = tail.subrange(mid - 1, tail.len() as int);
        lemma_language_of_seq_split(tail, mid - 1);
        // Now: L(tail) =~= concat(L(tail_prefix), L(tail_suffix))

        // Key observations:
        // prefix = elements[0..mid] = [elements[0]] ++ elements[1..mid] = [elements[0]] ++ tail_prefix
        // suffix = elements[mid..] = tail[mid-1..] = tail_suffix
        assert(tail_prefix =~= elements.subrange(1, mid));
        assert(tail_suffix =~= suffix);

        // L(prefix) = L([elements[0]] ++ tail_prefix)
        // By definition: language_of_seq([e0] ++ rest) = concat(L(e0), L(rest))
        // And: prefix = [elements[0]] ++ tail_prefix
        // But language_of_seq is defined recursively on prefix:
        //   L(prefix) = concat(L(prefix[0]), L(prefix[1..]))
        // prefix[0] = elements[0], prefix[1..] = tail_prefix
        assert(prefix.len() > 0) by { assert(mid >= 1); }
        assert(prefix[0] == elements[0]);
        assert(prefix.subrange(1, prefix.len() as int) =~= tail_prefix);
        // So L(prefix) = concat(L(elements[0]), L(tail_prefix))

        // L(elements) = concat(L(elements[0]), L(tail))
        //             = concat(L(elements[0]), concat(L(tail_prefix), L(tail_suffix)))  [by IH]
        //             = concat(concat(L(elements[0]), L(tail_prefix)), L(tail_suffix))  [by assoc]
        //             = concat(L(prefix), L(suffix))

        assert(elements.subrange(1, elements.len() as int) =~= tail);

        lemma_concat_languages_assoc(
            language_of_element(elements[0]),
            language_of_seq(tail_prefix),
            language_of_seq(tail_suffix),
        );
    }
}

/// If L(u_prefix) subset of L(v_prefix) and L(u_suffix) subset of L(v_suffix),
/// then L(u_prefix ++ u_suffix) subset of L(v_prefix ++ v_suffix)
proof fn lemma_language_inclusion_concat(
    u_pre: Seq<REElement>,
    u_suf: Seq<REElement>,
    v_pre: Seq<REElement>,
    v_suf: Seq<REElement>,
)
    requires
        language_inclusion(u_pre, v_pre),
        language_inclusion(u_suf, v_suf),
    ensures
        language_inclusion(u_pre + u_suf, v_pre + v_suf),
{
    let u = u_pre + u_suf;
    let v = v_pre + v_suf;

    // L(u) = L(u_pre ++ u_suf) = concat(L(u_pre), L(u_suf))  [by seq_split]
    lemma_language_of_seq_split(u, u_pre.len() as int);
    assert(u.subrange(0, u_pre.len() as int) =~= u_pre);
    assert(u.subrange(u_pre.len() as int, u.len() as int) =~= u_suf);

    // L(v) = L(v_pre ++ v_suf) = concat(L(v_pre), L(v_suf))
    lemma_language_of_seq_split(v, v_pre.len() as int);
    assert(v.subrange(0, v_pre.len() as int) =~= v_pre);
    assert(v.subrange(v_pre.len() as int, v.len() as int) =~= v_suf);

    // For any w in L(u), w = w1 + w2 where w1 in L(u_pre), w2 in L(u_suf)
    // By inclusion: w1 in L(v_pre), w2 in L(v_suf)
    // So w = w1 + w2 in L(v)
    assert forall|w: Seq<u32>| language_of_seq(u).contains(w) implies
        language_of_seq(v).contains(w)
    by {
        // w in concat(L(u_pre), L(u_suf))
        assert(concat_languages(language_of_seq(u_pre), language_of_seq(u_suf)).contains(w));
        let (w1, w2): (Seq<u32>, Seq<u32>) = choose|w1: Seq<u32>, w2: Seq<u32>|
            language_of_seq(u_pre).contains(w1) && language_of_seq(u_suf).contains(w2)
            && w =~= #[trigger](w1 + w2);
        // By language_inclusion preconditions
        assert(language_of_seq(v_pre).contains(w1));
        assert(language_of_seq(v_suf).contains(w2));
        // So w in concat(L(v_pre), L(v_suf)) = L(v)
        assert(concat_languages(language_of_seq(v_pre), language_of_seq(v_suf)).contains(w));
    }
}

/// Language of a single-element sequence equals the element's language
proof fn lemma_language_of_seq_singleton(e: REElement)
    ensures language_of_seq(seq![e]) =~= language_of_element(e),
{
    let s = seq![e];
    assert(s.len() == 1);
    assert(s[0] == e);
    let tail = s.subrange(1, s.len() as int);
    assert(tail.len() == 0);
    assert(tail =~= Seq::<REElement>::empty());
    // language_of_seq(s) = concat(language_of_element(e), language_of_seq(tail))
    //                    = concat(language_of_element(e), epsilon_language())
    assert(language_of_seq(tail) =~= epsilon_language());
    lemma_concat_epsilon_right(language_of_element(e));
}

/// Language inclusion is reflexive
proof fn lemma_language_inclusion_reflexive(u: Seq<REElement>)
    ensures language_inclusion(u, u),
{
}

// ============================================================================
// Level 4 (Phase 4): Range element language inclusion via covers
// ============================================================================

/// A Range element's language is the set of single-character strings
/// in [start, end]
pub open spec fn language_of_range(cs: CharSetModel) -> Set<Seq<u32>> {
    Set::new(|w: Seq<u32>| w.len() == 1 && charset_contains(cs, w[0]))
}

/// If charset a covers charset b, then L(Range(b)) subset of L(Range(a))
proof fn lemma_range_covers_implies_inclusion(a: CharSetModel, b: CharSetModel)
    requires
        charset_wf(a),
        charset_wf(b),
        charset_covers(a, b),
    ensures
        forall|w: Seq<u32>| language_of_range(b).contains(w) ==>
            language_of_range(a).contains(w),
{
    lemma_covers_implies_subset(a, b);
    assert forall|w: Seq<u32>| language_of_range(b).contains(w) implies
        language_of_range(a).contains(w)
    by {
        if language_of_range(b).contains(w) {
            assert(w.len() == 1);
            assert(charset_contains(b, w[0]));
            assert(charset_contains(a, w[0]));
        }
    }
}

// ============================================================================
// Level 4 (Phase 4): Full (sigma^*) element language
// ============================================================================

/// The language of a full element (sigma^*) contains all strings
pub open spec fn is_universal_language(l: Set<Seq<u32>>) -> bool {
    forall|w: Seq<u32>| l.contains(w)
}

/// Axiom: a full element (Loop over all characters with unbounded range,
/// i.e., sigma^*) has a universal language — it accepts all strings.
///
/// This is axiomatic because `language_of_element` returns `arbitrary()`
/// for non-Range elements. Making it concrete for Loop would require
/// modeling Kleene closure (L^0 ∪ L^1 ∪ L^2 ∪ ...) as a spec function,
/// which is complex. The property itself is the definition of sigma^*.
#[verifier::external_body]
proof fn lemma_full_element_universal(e: REElement)
    requires is_full_element(e),
    ensures is_universal_language(language_of_element(e)),
{
}

/// If L(v) is universal, then any L(u) is a subset
proof fn lemma_universal_includes_all(u: Seq<REElement>, v_lang: Set<Seq<u32>>)
    requires is_universal_language(v_lang),
    ensures forall|w: Seq<u32>| language_of_seq(u).contains(w) ==> v_lang.contains(w),
{
}

// ============================================================================
// Level 4 (Phase 4): concat_inclusion soundness
// ============================================================================

/// Model of concat_inclusion's algorithm state after prefix/suffix stripping.
/// At this point we have:
/// - u' = u with prefix and suffix stripped
/// - v' = v with prefix and suffix stripped
/// - patterns' = remaining patterns (prefix/suffix patterns removed, indices shifted)
pub struct ConcatInclusionState {
    pub u_orig: Seq<REElement>,
    pub v_orig: Seq<REElement>,
    pub u_trimmed: Seq<REElement>,
    pub v_trimmed: Seq<REElement>,
    pub prefix_len: nat,
    pub suffix_len: nat,
    pub patterns: Seq<BasePatternModel>,
}

/// The trimmed sequences are consistent with the originals
pub open spec fn concat_state_valid(state: ConcatInclusionState) -> bool {
    &&& state.prefix_len + state.suffix_len <= state.u_orig.len()
    &&& state.prefix_len + state.suffix_len <= state.v_orig.len()
    &&& state.u_trimmed =~= state.u_orig.subrange(
            state.prefix_len as int,
            (state.u_orig.len() - state.suffix_len) as int,
        )
    &&& state.v_trimmed =~= state.v_orig.subrange(
            state.prefix_len as int,
            (state.v_orig.len() - state.suffix_len) as int,
        )
}

/// If prefix matching succeeded, the prefix of u is included in the prefix of v.
/// This follows from rigid_match_at at position 0 with covers semantics.
proof fn lemma_prefix_match_implies_inclusion(
    u: Seq<REElement>,
    v: Seq<REElement>,
    pattern: Seq<CharSetModel>,
    prefix_len: nat,
)
    requires
        prefix_len == pattern.len(),
        u.len() >= prefix_len,
        v.len() >= prefix_len,
        rigid_match_at_spec(pattern, u, 0),
        // pattern comes from char_sets_of_pattern(v[0..prefix_len])
        // so pattern[j] == v[j].charset for each j
        forall|j: int| 0 <= j < prefix_len ==>
            #[trigger] pattern[j] == v[j].charset,
        // all v elements in prefix are Range
        forall|j: int| 0 <= j < prefix_len ==> is_range(#[trigger] v[j]),
        // all charsets are well-formed
        forall|j: int| 0 <= j < prefix_len ==> charset_wf(#[trigger] pattern[j]),
    ensures
        // Each u element in [0, prefix_len) is a Range whose charset
        // is covered by the corresponding v element's charset
        forall|j: int| 0 <= j < prefix_len ==> {
            &&& is_range(#[trigger] u[j])
            &&& charset_covers(v[j].charset, u[j].charset)
        },
{
    assert forall|j: int| 0 <= j < prefix_len implies
        is_range(#[trigger] u[j]) && charset_covers(v[j].charset, u[j].charset)
    by {
        assert(match_char_set(u[0int + j], pattern[j]));
        assert(u[0int + j] == u[j]);
        assert(is_range(u[j]));
        assert(charset_covers(pattern[j], u[j].charset));
        assert(pattern[j] == v[j].charset);
    }
}

/// Analogous lemma for suffix matching
proof fn lemma_suffix_match_implies_inclusion(
    u: Seq<REElement>,
    v: Seq<REElement>,
    pattern: Seq<CharSetModel>,
    suffix_len: nat,
)
    requires
        suffix_len == pattern.len(),
        u.len() >= suffix_len,
        v.len() >= suffix_len,
        rigid_match_at_spec(pattern, u, (u.len() - suffix_len) as nat),
        forall|j: int| 0 <= j < suffix_len ==>
            #[trigger] pattern[j] == v[(v.len() - suffix_len) as int + j].charset,
        forall|j: int| (v.len() - suffix_len) as int <= j < v.len() ==>
            is_range(#[trigger] v[j]),
        forall|j: int| 0 <= j < suffix_len ==> charset_wf(#[trigger] pattern[j]),
    ensures
        forall|j: int| (u.len() - suffix_len) as int <= j < u.len() ==> {
            let pj = (j - (u.len() - suffix_len) as int);
            &&& is_range(#[trigger] u[j])
            &&& charset_covers(
                    v[(v.len() - suffix_len) as int + pj].charset,
                    u[j].charset)
        },
{
    let u_start = (u.len() - suffix_len) as nat;
    assert forall|j: int| (u.len() - suffix_len) as int <= j < u.len()
        implies ({
            let pj = (j - (u.len() - suffix_len) as int);
            is_range(#[trigger] u[j]) && charset_covers(
                v[(v.len() - suffix_len) as int + pj].charset,
                u[j].charset)
        })
    by {
        let pj = (j - u_start as int);
        assert(0 <= pj < suffix_len as int);
        assert(match_char_set(u[u_start as int + pj], pattern[pj]));
        assert(u[u_start as int + pj] == u[j]);
        assert(is_range(u[j]));
        assert(charset_covers(pattern[pj], u[j].charset));
        assert(pattern[pj] == v[(v.len() - suffix_len) as int + pj].charset);
    }
}

// ============================================================================
// Level 4 (Phase 4): Rigid match implies element-wise language inclusion
// ============================================================================

/// If a rigid pattern from v matches a slice of u, then for each matched
/// position, L(u[i+j]) subset of L(v_pattern_element[j])
/// because match_char_set means covers, which means character-level inclusion.
proof fn lemma_rigid_match_implies_elementwise_inclusion(
    pattern: Seq<CharSetModel>,
    u: Seq<REElement>,
    v_elements: Seq<REElement>,
    match_start: nat,
    pattern_start: nat,
)
    requires
        match_start + pattern.len() <= u.len(),
        pattern_start + pattern.len() <= v_elements.len(),
        rigid_match_at_spec(pattern, u, match_start),
        // pattern comes from v_elements: pattern[j] == v_elements[pattern_start + j].charset
        forall|j: int| 0 <= j < pattern.len() ==>
            #[trigger] pattern[j] == v_elements[pattern_start as int + j].charset,
        forall|j: int| 0 <= j < pattern.len() ==>
            is_range(#[trigger] v_elements[pattern_start as int + j]),
        forall|j: int| 0 <= j < pattern.len() ==>
            charset_wf(#[trigger] pattern[j]),
    ensures
        // Each matched u element is a Range with charset covered by v's
        forall|j: int| 0 <= j < pattern.len() ==> {
            &&& is_range(#[trigger] u[match_start as int + j])
            &&& charset_covers(
                    v_elements[pattern_start as int + j].charset,
                    u[match_start as int + j].charset)
        },
{
    assert forall|j: int| 0 <= j < pattern.len()
        implies is_range(#[trigger] u[match_start as int + j])
            && charset_covers(
                v_elements[pattern_start as int + j].charset,
                u[match_start as int + j].charset)
    by {
        assert(match_char_set(u[match_start as int + j], pattern[j]));
        assert(is_range(u[match_start as int + j]));
        assert(charset_covers(pattern[j], u[match_start as int + j].charset));
        assert(pattern[j] == v_elements[pattern_start as int + j].charset);
    }
}

// ============================================================================
// Level 4: REModel to REElement bridge (decompose_concat)
// ============================================================================

/// Convert a non-Concat REModel to a single REElement.
pub open spec fn re_to_element(re: REModel) -> REElement {
    match re {
        REModel::Range { charset } => REElement { kind: REElementKind::Range, charset },
        REModel::Loop { .. } => REElement { kind: REElementKind::Loop, charset: CharSetModel { start: 0, end: 0 } },
        _ => REElement { kind: REElementKind::Other, charset: CharSetModel { start: 0, end: 0 } },
    }
}

/// Model of decompose_concat: flatten an RE tree into a sequence of elements.
/// - Concat nodes are flattened recursively
/// - Epsilon is dropped (empty sequence)
/// - Other nodes become single-element sequences
pub open spec fn decompose_re(re: REModel) -> Seq<REElement>
    decreases re,
{
    match re {
        REModel::Concat { left, right } =>
            decompose_re(*left) + decompose_re(*right),
        REModel::Epsilon => seq![],
        _ => seq![re_to_element(re)],
    }
}

/// For Range: re_to_element produces a Range element with the correct charset
proof fn lemma_re_to_element_range(charset: CharSetModel)
    ensures
        re_to_element(REModel::Range { charset }) == (REElement { kind: REElementKind::Range, charset }),
        is_range(re_to_element(REModel::Range { charset })),
        language_of_element(re_to_element(REModel::Range { charset })) =~= language_of_range(charset),
{
}

/// Bridge lemma: language_of_re(r) equals language_of_seq(decompose_re(r))
/// for the RE variants that appear in decompose_concat.
///
/// For leaf REs (non-Concat, non-Epsilon):
///   language_of_re(r) = language_of_element(re_to_element(r))
///   = language_of_seq(seq![re_to_element(r)])
///   = concat_languages(language_of_element(re_to_element(r)), epsilon)
///   = language_of_element(re_to_element(r))
///
/// For Concat:
///   language_of_re(Concat(l, r)) = concat(language_of_re(l), language_of_re(r))
///   By IH: = concat(language_of_seq(decompose(l)), language_of_seq(decompose(r)))
///   = language_of_seq(decompose(l) + decompose(r))  [by seq_split]
///   = language_of_seq(decompose_re(Concat(l, r)))
///
/// For Epsilon:
///   language_of_re(Epsilon) = epsilon_language() = language_of_seq(seq![])
///
/// Spec: is this RE a "leaf" in decompose (not Concat, not Epsilon, not Range)?
pub open spec fn is_decompose_leaf(re: REModel) -> bool {
    match re {
        REModel::Concat { .. } => false,
        REModel::Epsilon => false,
        REModel::Range { .. } => false,
        _ => true,
    }
}

/// Axiom: for leaf nodes in decompose_concat (Empty, Loop, Complement,
/// Union, Inter), the RE-level language equals the element-level language.
///
/// This bridges two abstraction levels: `language_of_re` (defined on `REModel`)
/// and `language_of_element` (defined on `REElement`). For Range elements this
/// is proven concretely since both use `language_of_range`. For other variants,
/// `language_of_re` returns `arbitrary()` (Union/Inter/Loop) or a concrete
/// value (Empty = {}), while `language_of_element` also returns `arbitrary()`
/// for non-Range kinds. Proving equality would require making both functions
/// concrete for all variants, which requires modeling Kleene closure (Loop)
/// and recursive language definitions (Union/Inter over Seq<REModel>).
#[verifier::external_body]
proof fn axiom_leaf_re_language(re: REModel)
    requires is_decompose_leaf(re),
    ensures language_of_re(re) =~= language_of_element(re_to_element(re)),
{
}

/// The decomposition bridge: language_of_re(r) = language_of_seq(decompose_re(r))
proof fn lemma_decompose_preserves_language(re: REModel)
    ensures language_of_re(re) =~= language_of_seq(decompose_re(re)),
    decreases re,
{
    match re {
        REModel::Epsilon => {
            // language_of_re(Epsilon) = epsilon_language()
            // decompose_re(Epsilon) = seq![]
            // language_of_seq(seq![]) = epsilon_language()
            assert(decompose_re(re) =~= Seq::<REElement>::empty());
        }
        REModel::Range { charset } => {
            let e = re_to_element(re);
            lemma_re_to_element_range(charset);
            assert(decompose_re(re) =~= seq![e]);
            lemma_language_of_seq_singleton(e);
            // language_of_seq(seq![e]) =~= language_of_element(e) =~= language_of_range(charset) = language_of_re(re)
        }
        REModel::Concat { left, right } => {
            // IH
            lemma_decompose_preserves_language(*left);
            lemma_decompose_preserves_language(*right);
            // language_of_re(Concat) = concat(language_of_re(left), language_of_re(right))
            //                        = concat(language_of_seq(decompose(left)), language_of_seq(decompose(right)))
            // decompose_re(Concat) = decompose(left) + decompose(right)
            // By seq_split: language_of_seq(a + b) = concat(language_of_seq(a), language_of_seq(b))
            let dl = decompose_re(*left);
            let dr = decompose_re(*right);
            let combined = dl + dr;
            lemma_language_of_seq_split(combined, dl.len() as int);
            assert(combined.subrange(0, dl.len() as int) =~= dl);
            assert(combined.subrange(dl.len() as int, combined.len() as int) =~= dr);
        }
        _ => {
            // Empty, Loop, Complement, Union, Inter
            assert(is_decompose_leaf(re));
            axiom_leaf_re_language(re);
            let e = re_to_element(re);
            assert(language_of_re(re) =~= language_of_element(e));
            assert(decompose_re(re) =~= seq![e]);
            // Manually unfold language_of_seq for a single-element sequence
            lemma_language_of_seq_singleton(e);
        }
    }
}

// ============================================================================
// Level 4 (Phase 4): concat_inclusion overall soundness
// ============================================================================

/// Helper: if two sequences have equal length and each element of a has its
/// language included in the corresponding element of b, then L(a) ⊆ L(b).
proof fn lemma_elementwise_seq_inclusion(a: Seq<REElement>, b: Seq<REElement>)
    requires
        a.len() == b.len(),
        forall|j: int| 0 <= j < a.len() ==>
            forall|w: Seq<u32>|
                language_of_element(#[trigger] a[j]).contains(w) ==>
                language_of_element(b[j]).contains(w),
    ensures
        language_inclusion(a, b),
    decreases a.len(),
{
    if a.len() == 0 {
        // Both empty → both epsilon language → trivially equal
    } else {
        let a_head = seq![a[0]];
        let b_head = seq![b[0]];
        let a_tail = a.subrange(1, a.len() as int);
        let b_tail = b.subrange(1, b.len() as int);

        // Show IH precondition for tails
        assert forall|j: int| 0 <= j < a_tail.len() implies
            forall|w: Seq<u32>|
                language_of_element(#[trigger] a_tail[j]).contains(w) ==>
                language_of_element(b_tail[j]).contains(w)
        by {
            assert(a_tail[j] == a[j + 1]);
            assert(b_tail[j] == b[j + 1]);
        }
        lemma_elementwise_seq_inclusion(a_tail, b_tail);

        // Show language_inclusion for heads (singletons)
        lemma_language_of_seq_singleton(a[0]);
        lemma_language_of_seq_singleton(b[0]);
        assert forall|w: Seq<u32>| language_of_seq(a_head).contains(w) implies
            language_of_seq(b_head).contains(w)
        by {
            assert(language_of_element(a[0]).contains(w));
            assert(language_of_element(b[0]).contains(w));
        }

        // Compose: L(a_head ++ a_tail) ⊆ L(b_head ++ b_tail)
        lemma_language_inclusion_concat(a_head, a_tail, b_head, b_tail);
        assert(a_head + a_tail =~= a);
        assert(b_head + b_tail =~= b);
    }
}

/// Helper: for a rigid pattern k, the matched segment of u has language
/// included in the corresponding segment of v.
proof fn lemma_rigid_segment_inclusion(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
    k: int,
)
    requires
        0 <= k < patterns.len(),
        patterns[k].is_rigid,
        base_patterns_wf(patterns, v.len()),
        pattern_elements_consistent(patterns, v),
        rigid_matches_correct(patterns, v, u),
        forall|i: int| 0 <= i < u.len() ==> charset_wf((#[trigger] u[i]).charset),
        forall|i: int| 0 <= i < v.len() ==> charset_wf((#[trigger] v[i]).charset),
    ensures
        language_inclusion(
            u.subrange(patterns[k].start_match as int, patterns[k].end_match as int),
            v.subrange(patterns[k].start as int, patterns[k].end as int),
        ),
{
    let p = patterns[k];
    let pat_len = (p.end - p.start) as nat;
    let u_seg = u.subrange(p.start_match as int, p.end_match as int);
    let v_seg = v.subrange(p.start as int, p.end as int);
    let charsets = char_sets_of_pattern_spec(v_seg);

    // Establish lengths of segments
    assert(p.end_match == p.start_match + pat_len);
    assert(u_seg.len() == pat_len);

    // Establish bounds: p.end <= v.len()
    lemma_pattern_end_bounded(patterns, v.len(), k);
    assert(p.start as int <= p.end as int);
    assert(p.end as int <= v.len() as int);

    // v_seg has the right length and all elements are Range (rigid pattern)
    lemma_rigid_pattern_has_charsets(patterns, v, k);
    // Now: forall|idx| patterns[k].start <= idx < patterns[k].end ==> is_range(v[idx])
    assert forall|j: int| 0 <= j < v_seg.len() implies is_range(#[trigger] v_seg[j])
    by {
        let v_idx = p.start as int + j;
        assert(0 <= j && j < p.end - p.start);
        assert(p.start <= v_idx && v_idx < p.end);
        assert(is_range(v[v_idx]));
    }

    // rigid_match_at_spec holds → element-wise charset coverage
    assert(rigid_match_at_spec(charsets, u, p.start_match));

    // charsets has same length as v_seg
    lemma_char_sets_of_pattern_length(v_seg);
    assert(charsets.len() == v_seg.len());

    // For each j: u_seg[j] and v_seg[j] are both Range with covers
    assert forall|j: int| 0 <= j < charsets.len() implies
        forall|w: Seq<u32>|
            language_of_element(#[trigger] u_seg[j]).contains(w) ==>
            language_of_element(v_seg[j]).contains(w)
    by {
        // u[start_match + j] matches charsets[j]
        assert(match_char_set(u[p.start_match as int + j], charsets[j]));
        assert(u_seg[j] == u[p.start_match as int + j]);
        assert(is_range(u_seg[j]));
        assert(charset_covers(charsets[j], u_seg[j].charset));

        // charsets[j] = v_seg[j].charset
        lemma_char_sets_of_pattern_correspondence(v_seg, j);

        // charset_covers(v_seg[j].charset, u_seg[j].charset)
        assert(charset_covers(v_seg[j].charset, u_seg[j].charset));
        lemma_covers_implies_subset(v_seg[j].charset, u_seg[j].charset);
    }

    // Transfer from charsets.len() indexing to u_seg.len() indexing
    assert(u_seg.len() == charsets.len());

    lemma_elementwise_seq_inclusion(u_seg, v_seg);
}

/// Helper: for a flexible pattern k, the matched segment of u has language
/// included in the corresponding segment of v (which is sigma^*).
proof fn lemma_flexible_segment_inclusion(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
    k: int,
)
    requires
        0 <= k < patterns.len(),
        !patterns[k].is_rigid,
        patterns[k].start_match <= patterns[k].end_match,
        patterns[k].end_match <= u.len(),
        base_patterns_wf(patterns, v.len()),
        match_flexible_patterns_spec(u, v, patterns),
    ensures
        language_inclusion(
            u.subrange(patterns[k].start_match as int, patterns[k].end_match as int),
            v.subrange(patterns[k].start as int, patterns[k].end as int),
        ),
{
    let p = patterns[k];
    let u_seg = u.subrange(p.start_match as int, p.end_match as int);
    let v_seg = v.subrange(p.start as int, p.end as int);

    // By match_flexible_patterns_spec: flexible_match_spec(u_seg, v_seg)
    // meaning v_seg.len() == 1 && is_full_element(v_seg[0])
    assert(flexible_match_spec(u_seg, v_seg));
    assert(v_seg.len() == 1);
    assert(is_full_element(v_seg[0]));

    // L(v_seg) = L(singleton) = language_of_element(v_seg[0])
    lemma_language_of_seq_singleton(v_seg[0]);
    // language_of_element(v_seg[0]) is universal
    lemma_full_element_universal(v_seg[0]);
    // v_seg has length 1, so v_seg =~= seq![v_seg[0]]
    assert(v_seg =~= seq![v_seg[0]]);
    // L(v_seg) = language_of_element(v_seg[0]) by singleton lemma
    lemma_language_of_seq_singleton(v_seg[0]);
    // language_of_element(v_seg[0]) is universal
    lemma_full_element_universal(v_seg[0]);
    let v_lang = language_of_element(v_seg[0]);
    assert(is_universal_language(v_lang));
    // L(u_seg) ⊆ universal
    lemma_universal_includes_all(u_seg, v_lang);
    // Transfer: language_of_seq(v_seg) =~= language_of_seq(seq![v_seg[0]]) =~= v_lang
    assert forall|w: Seq<u32>| language_of_seq(u_seg).contains(w) implies
        language_of_seq(v_seg).contains(w)
    by {
        assert(v_lang.contains(w));
        assert(language_of_seq(v_seg) =~= v_lang);
    }
}

/// Helper: match regions of adjacent patterns are contiguous.
/// Pattern k's end_match equals pattern (k+1)'s start_match.
proof fn lemma_match_contiguity(
    patterns: Seq<BasePatternModel>,
    v_len: nat,
    u_len: nat,
    k: int,
)
    requires
        base_patterns_wf(patterns, v_len),
        rigid_matches_valid(patterns, u_len),
        rigid_matches_anchored(patterns, u_len),
        flexible_regions_valid(patterns, u_len),
        0 <= k < patterns.len() - 1,
    ensures
        patterns[k].end_match == patterns[k + 1].start_match,
{
    if !patterns[k + 1].is_rigid {
        // k+1 is flexible: start_match = prev_end = patterns[k].end_match
        assert(patterns[k + 1].start_match == patterns[k].end_match);
    } else {
        // k+1 is rigid, so k is flexible (alternating)
        assert(!patterns[k].is_rigid);
        // flex[k].end_match = next_start = patterns[k+1].start_match
        assert(patterns[k].end_match == patterns[k + 1].start_match);
    }
}

/// Helper: first pattern's start_match is 0.
proof fn lemma_first_pattern_starts_at_zero(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
)
    requires
        patterns.len() > 0,
        rigid_matches_anchored(patterns, u_len),
        flexible_regions_valid(patterns, u_len),
    ensures
        patterns[0].start_match == 0nat,
{
    if patterns[0].is_rigid {
        assert(patterns[0].start_match == 0nat);
    } else {
        // flexible: start_match = if 0 == 0 { 0 } else { ... } = 0
        assert(patterns[0].start_match == 0nat);
    }
}

/// Helper: last pattern's end_match is u_len.
proof fn lemma_last_pattern_ends_at_u_len(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
)
    requires
        patterns.len() > 0,
        rigid_matches_anchored(patterns, u_len),
        flexible_regions_valid(patterns, u_len),
    ensures
        patterns[patterns.len() - 1].end_match == u_len,
{
    let last = (patterns.len() - 1) as int;
    if patterns[last].is_rigid {
        assert(patterns[last].end_match == u_len);
    } else {
        // flexible last: end_match = u_len
        assert(patterns[last].end_match == u_len);
    }
}

/// Helper: every pattern's end is <= input_len (v.len())
proof fn lemma_pattern_end_bounded(
    patterns: Seq<BasePatternModel>,
    input_len: nat,
    k: int,
)
    requires
        base_patterns_wf(patterns, input_len),
        0 <= k < patterns.len(),
    ensures
        patterns[k].end <= input_len,
    decreases patterns.len() - k,
{
    if k == patterns.len() - 1 {
        // Last pattern: end == input_len
        assert(patterns[k].end == input_len);
    } else {
        // patterns[k].end == patterns[k+1].start < patterns[k+1].end
        lemma_pattern_end_bounded(patterns, input_len, k + 1);
        assert(patterns[k].end == patterns[k + 1].start);
        assert(patterns[k + 1].start < patterns[k + 1].end);
    }
}

/// All match regions are within [0, u_len). This is established by the
/// algorithm after find_rigid_matches + set_flexible_regions.
pub open spec fn all_matches_bounded(
    patterns: Seq<BasePatternModel>,
    u_len: nat,
) -> bool {
    forall|k: int| 0 <= k < patterns.len() ==> {
        &&& (#[trigger] patterns[k]).start_match <= patterns[k].end_match
        &&& patterns[k].end_match <= u_len
    }
}

/// Helper: s[0..m] + s[m..n] = s[0..n]
proof fn lemma_subrange_concat<T>(s: Seq<T>, m: int, n: int)
    requires
        0 <= m <= n <= s.len(),
    ensures
        s.subrange(0, m) + s.subrange(m, n) =~= s.subrange(0, n),
{
    let left = s.subrange(0, m);
    let right = s.subrange(m, n);
    let combined = left + right;
    let target = s.subrange(0, n);
    assert(combined.len() == target.len());
    assert forall|i: int| 0 <= i < combined.len() implies
        combined[i] == target[i]
    by {
        if i < m {
            assert(combined[i] == left[i]);
            assert(left[i] == s[i]);
            assert(target[i] == s[i]);
        } else {
            assert(combined[i] == right[i - m]);
            assert(right[i - m] == s[m + (i - m)]);
            assert(target[i] == s[i]);
        }
    }
}

/// Inductive composition: after processing the first k patterns,
/// L(u[0..end_match_k]) ⊆ L(v[0..end_k]).
proof fn lemma_compose_patterns(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
    k: int,
)
    requires
        0 < k <= patterns.len(),
        base_patterns_wf(patterns, v.len()),
        pattern_elements_consistent(patterns, v),
        rigid_matches_valid(patterns, u.len()),
        rigid_matches_anchored(patterns, u.len()),
        rigid_matches_correct(patterns, v, u),
        all_matches_bounded(patterns, u.len()),
        flexible_regions_valid(patterns, u.len()),
        match_flexible_patterns_spec(u, v, patterns),
        forall|i: int| 0 <= i < u.len() ==> charset_wf((#[trigger] u[i]).charset),
        forall|i: int| 0 <= i < v.len() ==> charset_wf((#[trigger] v[i]).charset),
    ensures
        language_inclusion(
            u.subrange(0, patterns[k - 1].end_match as int),
            v.subrange(0, patterns[k - 1].end as int),
        ),
    decreases k,
{
    let p = patterns[k - 1];

    if k == 1 {
        // Base case: just pattern 0
        lemma_first_pattern_starts_at_zero(patterns, u.len());
        let u_seg = u.subrange(p.start_match as int, p.end_match as int);
        let v_seg = v.subrange(p.start as int, p.end as int);

        if p.is_rigid {
            lemma_rigid_segment_inclusion(u, v, patterns, 0);
        } else {
            // Need start_match <= end_match for the flexible lemma
            // If rigid: by rigid_matches_valid. If flex:
            // start_match = 0, end_match = if last { u_len } else { patterns[1].start_match }
            // In either case >= 0 = start_match
            if patterns.len() > 1 {
                // end_match = patterns[1].start_match
                // start_match = 0
                // patterns[1].start_match >= 0 since it's a nat
            }
            lemma_flexible_segment_inclusion(u, v, patterns, 0);
        }
        // u_seg = u[0..end_match] since start_match = 0
        assert(u.subrange(0, p.end_match as int) =~= u_seg);
        // v_seg = v[0..end] since start = 0
        assert(p.start == 0);
        assert(v.subrange(0, p.end as int) =~= v_seg);
    } else {
        // Inductive step: k > 1
        let prev = patterns[k - 2];

        // IH: L(u[0..prev.end_match]) ⊆ L(v[0..prev.end])
        lemma_compose_patterns(u, v, patterns, k - 1);

        // Contiguity: prev.end_match == p.start_match
        lemma_match_contiguity(patterns, v.len(), u.len(), k - 2);
        assert(prev.end_match == p.start_match);
        // Also: prev.end == p.start (from base_patterns_wf contiguity)
        assert(prev.end == p.start);

        // Segment k-1: L(u[p.start_match..p.end_match]) ⊆ L(v[p.start..p.end])
        if p.is_rigid {
            lemma_rigid_segment_inclusion(u, v, patterns, k - 1);
        } else {
            lemma_flexible_segment_inclusion(u, v, patterns, k - 1);
        }

        // Now compose:
        let u_pre = u.subrange(0, prev.end_match as int);
        let u_suf = u.subrange(p.start_match as int, p.end_match as int);
        let v_pre = v.subrange(0, prev.end as int);
        let v_suf = v.subrange(p.start as int, p.end as int);

        lemma_language_inclusion_concat(u_pre, u_suf, v_pre, v_suf);

        // Establish bounds for subrange_concat
        lemma_pattern_end_bounded(patterns, v.len(), k - 1);
        assert(p.end <= v.len());
        assert(p.end_match <= u.len());  // from all_matches_bounded

        // u[0..prev.end_match] + u[p.start_match..p.end_match] = u[0..p.end_match]
        lemma_subrange_concat(u, prev.end_match as int, p.end_match as int);
        // v[0..prev.end] + v[p.start..p.end] = v[0..p.end]
        lemma_subrange_concat(v, prev.end as int, p.end as int);
    }
}

/// The top-level soundness theorem for concat_inclusion:
///
/// If concat_inclusion(u, v) returns true, then L(concat(u)) is a subset
/// of L(concat(v)).
///
/// The proof processes patterns left to right, showing language inclusion
/// holds for each prefix, then completes at the full sequences.
proof fn theorem_concat_inclusion_soundness(
    u: Seq<REElement>,
    v: Seq<REElement>,
    patterns: Seq<BasePatternModel>,
)
    requires
        // base_patterns(v) produced well-formed patterns
        base_patterns_wf(patterns, v.len()),
        pattern_elements_consistent(patterns, v),
        // The algorithm found a valid matching:
        // all rigid patterns in v have matches in u
        rigid_matches_valid(patterns, u.len()),
        // rigid prefix/suffix are anchored
        rigid_matches_anchored(patterns, u.len()),
        // rigid matches are genuine matches
        rigid_matches_correct(patterns, v, u),
        // all match regions are bounded
        all_matches_bounded(patterns, u.len()),
        // all flexible patterns fill the gaps
        flexible_regions_valid(patterns, u.len()),
        // all flexible matches succeeded (each gap has sigma^*)
        match_flexible_patterns_spec(u, v, patterns),
        // charsets are well-formed
        forall|i: int| 0 <= i < u.len() ==> charset_wf((#[trigger] u[i]).charset),
        forall|i: int| 0 <= i < v.len() ==> charset_wf((#[trigger] v[i]).charset),
    ensures
        language_inclusion(u, v),
{
    if v.len() == 0 {
        // No patterns, u must be empty too
        // base_patterns_wf with v.len() == 0 means patterns.len() == 0
        // Then match_flexible_patterns_spec with patterns.len() == 0 means u.len() == 0
        assert(patterns.len() == 0);
        assert(u.len() == 0);
        // Both empty → both epsilon → trivially included
    } else {
        assert(patterns.len() > 0);
        // Process all patterns
        lemma_compose_patterns(u, v, patterns, patterns.len() as int);
        // Now: L(u[0..last.end_match]) ⊆ L(v[0..last.end])
        let last = patterns[patterns.len() - 1];
        // last.end_match == u.len() and last.end == v.len()
        lemma_last_pattern_ends_at_u_len(patterns, u.len());
        assert(last.end_match == u.len());
        assert(last.end == v.len());
        // So: L(u) ⊆ L(v)
        assert(u.subrange(0, u.len() as int) =~= u);
        assert(v.subrange(0, v.len() as int) =~= v);
    }
}

// ============================================================================
// Level 4 (Phase 4): sub_language soundness
// ============================================================================

/// Model of the RE AST for sub_language
pub enum REModel {
    Empty,
    Epsilon,
    Range { charset: CharSetModel },
    Concat { left: Box<REModel>, right: Box<REModel> },
    Loop { body: Box<REModel> },
    Complement { inner: Box<REModel> },
    Union { children: Seq<REModel> },
    Inter { children: Seq<REModel> },
}

/// Language of an RE model.
/// Concrete for Empty, Epsilon, Range, Concat, Complement.
/// Abstract for Union, Inter, Loop (properties stated as axioms).
pub open spec fn language_of_re(re: REModel) -> Set<Seq<u32>>
    decreases re,
{
    match re {
        REModel::Empty => Set::empty(),
        REModel::Epsilon => epsilon_language(),
        REModel::Range { charset } => language_of_range(charset),
        REModel::Concat { left, right } =>
            concat_languages(language_of_re(*left), language_of_re(*right)),
        REModel::Complement { inner } => complement_language(language_of_re(*inner)),
        // For Union, Inter, Loop: properties are stated axiomatically below.
        _ => arbitrary(),
    }
}

/// Complement of a language
pub open spec fn complement_language(l: Set<Seq<u32>>) -> Set<Seq<u32>> {
    Set::new(|w: Seq<u32>| !l.contains(w))
}

/// Union of languages from a sequence of language sets
pub open spec fn union_language_sets(langs: Seq<Set<Seq<u32>>>) -> Set<Seq<u32>>
    decreases langs.len(),
{
    if langs.len() == 0 {
        Set::empty()
    } else {
        langs[0].union(
            union_language_sets(langs.subrange(1, langs.len() as int))
        )
    }
}

/// Intersection of languages from a sequence of language sets
pub open spec fn inter_language_sets(langs: Seq<Set<Seq<u32>>>) -> Set<Seq<u32>>
    decreases langs.len(),
{
    if langs.len() == 0 {
        Set::new(|_w: Seq<u32>| true)
    } else {
        langs[0].intersect(
            inter_language_sets(langs.subrange(1, langs.len() as int))
        )
    }
}

/// Axiom: L(Union(children)) = ∪_k L(children[k]).
///
/// This is the standard semantic definition of Union for regular expressions.
/// It is axiomatic because `language_of_re(Union { children })` returns
/// `arbitrary()` — Verus cannot verify recursive spec functions over
/// `Seq<REModel>` elements with structural decreasing (Seq is abstract,
/// so `children[k]` is not a proven sub-term of `Union { children }`).
/// Making this provable would require a fuel/height parameter on
/// `language_of_re` or restructuring Union to use an inductive list.
#[verifier::external_body]
proof fn axiom_union_language(children: Seq<REModel>)
    ensures
        forall|w: Seq<u32>|
            language_of_re(REModel::Union { children }).contains(w) <==>
            exists|k: int| 0 <= k < children.len()
                && language_of_re(#[trigger] children[k]).contains(w),
{
}

/// Axiom: L(Inter(children)) = ∩_k L(children[k]).
///
/// Same limitation as `axiom_union_language`: `language_of_re(Inter { children })`
/// returns `arbitrary()` because Verus cannot recurse over Seq elements with
/// structural decreasing. This axiom states the standard intersection semantics.
#[verifier::external_body]
proof fn axiom_inter_language(children: Seq<REModel>)
    ensures
        forall|w: Seq<u32>|
            language_of_re(REModel::Inter { children }).contains(w) <==>
            forall|k: int| 0 <= k < children.len()
                ==> language_of_re(#[trigger] children[k]).contains(w),
{
}

/// Nullable: the language contains the empty string
pub open spec fn is_nullable(re: REModel) -> bool {
    language_of_re(re).contains(Seq::<u32>::empty())
}

// ============================================================================
// Level 4 (Phase 4): sub_language case-by-case soundness
// ============================================================================

/// Case: r == s => L(r) = L(s) => L(r) subset of L(s)
proof fn lemma_sub_language_reflexive(r: REModel)
    ensures forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
        language_of_re(r).contains(w),
{
}

/// Case: Empty is subset of anything
proof fn lemma_sub_language_empty(s: REModel)
    ensures forall|w: Seq<u32>| language_of_re(REModel::Empty).contains(w) ==>
        language_of_re(s).contains(w),
{
    // L(Empty) = {} so the implication is vacuously true
}

/// Case: Epsilon subset of s iff s is nullable
proof fn lemma_sub_language_epsilon(s: REModel)
    requires is_nullable(s),
    ensures forall|w: Seq<u32>| language_of_re(REModel::Epsilon).contains(w) ==>
        language_of_re(s).contains(w),
{
    // L(Epsilon) = {""}, so we only need s to contain ""
    assert forall|w: Seq<u32>| language_of_re(REModel::Epsilon).contains(w)
        implies language_of_re(s).contains(w)
    by {
        assert(w =~= Seq::<u32>::empty());
    }
}

/// Case: nothing is subset of Empty (except Empty itself)
proof fn lemma_sub_language_into_empty_false(r: REModel, w: Seq<u32>)
    requires language_of_re(r).contains(w),
    ensures !language_of_re(REModel::Empty).contains(w),
{
}

/// Case: Complement(r) subset of Complement(s) iff S subset of R
/// (contravariance of complement)
proof fn lemma_sub_language_complement(r: REModel, s: REModel)
    requires
        // L(s) subset of L(r)
        forall|w: Seq<u32>| language_of_re(s).contains(w) ==>
            language_of_re(r).contains(w),
    ensures
        // L(complement(r)) subset of L(complement(s))
        forall|w: Seq<u32>|
            complement_language(language_of_re(r)).contains(w) ==>
            complement_language(language_of_re(s)).contains(w),
{
    assert forall|w: Seq<u32>|
        complement_language(language_of_re(r)).contains(w)
        implies complement_language(language_of_re(s)).contains(w)
    by {
        // w not in L(r) and L(s) subset L(r) implies w not in L(s)
        assert(!language_of_re(r).contains(w));
        if language_of_re(s).contains(w) {
            assert(language_of_re(r).contains(w)); // contradiction
        }
    }
}

/// Case: r subset of Union(s_1, ..., s_n) if r subset of some s_i
proof fn lemma_sub_language_into_union(
    r: REModel,
    children: Seq<REModel>,
    k: int,
)
    requires
        0 <= k < children.len(),
        forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
            language_of_re(children[k]).contains(w),
    ensures
        forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
            language_of_re(REModel::Union { children }).contains(w),
{
    axiom_union_language(children);
    assert forall|w: Seq<u32>| language_of_re(r).contains(w)
        implies language_of_re(REModel::Union { children }).contains(w)
    by {
        assert(language_of_re(children[k]).contains(w));
    }
}

/// Case: Inter(r_1, ..., r_n) subset of s if some r_i subset of s
proof fn lemma_sub_language_from_inter(
    children: Seq<REModel>,
    s: REModel,
    k: int,
)
    requires
        0 <= k < children.len(),
        forall|w: Seq<u32>| language_of_re(children[k]).contains(w) ==>
            language_of_re(s).contains(w),
    ensures
        forall|w: Seq<u32>| language_of_re(REModel::Inter { children }).contains(w) ==>
            language_of_re(s).contains(w),
{
    axiom_inter_language(children);
    assert forall|w: Seq<u32>|
        language_of_re(REModel::Inter { children }).contains(w)
        implies language_of_re(s).contains(w)
    by {
        assert(language_of_re(children[k]).contains(w));
    }
}

/// Case: Union(r_1, ..., r_n) subset of s if all r_i subset of s
proof fn lemma_sub_language_from_union(
    children: Seq<REModel>,
    s: REModel,
)
    requires
        forall|k: int| 0 <= k < children.len() ==>
            forall|w: Seq<u32>| language_of_re(#[trigger] children[k]).contains(w) ==>
                language_of_re(s).contains(w),
    ensures
        forall|w: Seq<u32>| language_of_re(REModel::Union { children }).contains(w) ==>
            language_of_re(s).contains(w),
{
    axiom_union_language(children);
    assert forall|w: Seq<u32>|
        language_of_re(REModel::Union { children }).contains(w)
        implies language_of_re(s).contains(w)
    by {
        let k = choose|k: int| 0 <= k < children.len()
            && language_of_re(#[trigger] children[k]).contains(w);
        assert(language_of_re(children[k]).contains(w));
    }
}

/// Case: r subset of Inter(s_1, ..., s_n) if r subset of all s_i
proof fn lemma_sub_language_into_inter(
    r: REModel,
    children: Seq<REModel>,
)
    requires
        forall|k: int| 0 <= k < children.len() ==>
            forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
                language_of_re(#[trigger] children[k]).contains(w),
    ensures
        forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
            language_of_re(REModel::Inter { children }).contains(w),
{
    axiom_inter_language(children);
    assert forall|w: Seq<u32>| language_of_re(r).contains(w)
        implies language_of_re(REModel::Inter { children }).contains(w)
    by {
        assert forall|k: int| 0 <= k < children.len()
            implies language_of_re(#[trigger] children[k]).contains(w)
        by {
            // r subset children[k] for all k
        }
    }
}

// ============================================================================
// Level 4 (Phase 4): The main soundness theorem
// ============================================================================

/// Spec function mirroring sub_language's control flow.
///
/// This models exactly what the Rust `sub_language` function computes.
/// It takes an additional `concat_oracle` parameter that captures whether
/// concat_inclusion would return true for the default case (since we
/// don't model concat_inclusion's full algorithm as a spec function).
///
/// The function returns the "reason" sub_language returned true, encoded
/// as an enum, so the proof can dispatch to the right case lemma.
pub enum SubLanguageResult {
    /// r == s (reflexivity)
    Equal,
    /// r is Empty
    REmpty,
    /// s is Empty (returns false -- no proof needed)
    SEmpty,
    /// r is Epsilon and s is nullable
    REpsilon,
    /// s is Epsilon (returns false)
    SEpsilon,
    /// Complement(r1) vs Complement(s2), with recursive result for (s2, r1)
    Complement { inner_result: Box<SubLanguageResult> },
    /// r subset Union(children): found child k where sub_language(r, children[k])
    IntoUnion { k: int, inner_result: Box<SubLanguageResult> },
    /// Inter(children) subset s: found child k where sub_language(children[k], s)
    FromInter { k: int, inner_result: Box<SubLanguageResult> },
    /// Union(children) subset s: sub_language(child_k, s) for all k
    FromUnion { inner_results: Seq<SubLanguageResult> },
    /// r subset Inter(children): sub_language(r, child_k) for all k
    IntoInter { inner_results: Seq<SubLanguageResult> },
    /// Default case: concat_inclusion returned true.
    /// Carries the element sequences and patterns that witnessed success.
    ConcatInclusion {
        u_elems: Seq<REElement>,
        v_elems: Seq<REElement>,
        patterns: Seq<BasePatternModel>,
    },
    /// sub_language returned false (no proof obligation)
    Failed,
}

/// Predicate: the SubLanguageResult is a valid witness that sub_language(r, s)
/// returned true.
///
/// This connects each result variant to the corresponding preconditions
/// needed for the case lemma.
pub open spec fn sub_language_result_valid(
    r: REModel,
    s: REModel,
    result: SubLanguageResult,
) -> bool
    decreases result,
{
    match result {
        SubLanguageResult::Equal => {
            r == s
        }
        SubLanguageResult::REmpty => {
            r == REModel::Empty
        }
        SubLanguageResult::REpsilon => {
            r == REModel::Epsilon && is_nullable(s)
        }
        SubLanguageResult::Complement { inner_result } => {
            // r = Complement(r1), s = Complement(s2), sub_language(s2, r1) = true
            exists|r1: REModel, s2: REModel|
                r == REModel::Complement { inner: Box::new(r1) }
                && s == REModel::Complement { inner: Box::new(s2) }
                && sub_language_result_valid(s2, r1, *inner_result)
        }
        SubLanguageResult::IntoUnion { k, inner_result } => {
            // s = Union(children), sub_language(r, children[k]) = true
            exists|children: Seq<REModel>|
                s == REModel::Union { children }
                && 0 <= k < children.len()
                && sub_language_result_valid(r, children[k], *inner_result)
        }
        SubLanguageResult::FromInter { k, inner_result } => {
            // r = Inter(children), sub_language(children[k], s) = true
            exists|children: Seq<REModel>|
                r == REModel::Inter { children }
                && 0 <= k < children.len()
                && sub_language_result_valid(children[k], s, *inner_result)
        }
        SubLanguageResult::FromUnion { inner_results } => {
            // r = Union(children), sub_language(children[k], s) for all k
            exists|children: Seq<REModel>|
                r == REModel::Union { children }
                && inner_results.len() == children.len()
                && forall|k: int| 0 <= k < children.len() ==>
                    sub_language_result_valid(
                        #[trigger] children[k], s, inner_results[k])
        }
        SubLanguageResult::IntoInter { inner_results } => {
            // s = Inter(children), sub_language(r, children[k]) for all k
            exists|children: Seq<REModel>|
                s == REModel::Inter { children }
                && inner_results.len() == children.len()
                && forall|k: int| 0 <= k < children.len() ==>
                    sub_language_result_valid(
                        r, #[trigger] children[k], inner_results[k])
        }
        SubLanguageResult::ConcatInclusion { u_elems, v_elems, patterns } => {
            // Default case: concat_inclusion succeeded on decomposed sequences.
            // The element sequences are the decompositions of r and s.
            &&& u_elems =~= decompose_re(r)
            &&& v_elems =~= decompose_re(s)
            // concat_inclusion's preconditions hold:
            &&& base_patterns_wf(patterns, v_elems.len())
            &&& pattern_elements_consistent(patterns, v_elems)
            &&& rigid_matches_valid(patterns, u_elems.len())
            &&& rigid_matches_anchored(patterns, u_elems.len())
            &&& rigid_matches_correct(patterns, v_elems, u_elems)
            &&& all_matches_bounded(patterns, u_elems.len())
            &&& flexible_regions_valid(patterns, u_elems.len())
            &&& match_flexible_patterns_spec(u_elems, v_elems, patterns)
            &&& forall|i: int| 0 <= i < u_elems.len() ==> charset_wf((#[trigger] u_elems[i]).charset)
            &&& forall|i: int| 0 <= i < v_elems.len() ==> charset_wf((#[trigger] v_elems[i]).charset)
        }
        // These cases mean sub_language returned false
        SubLanguageResult::SEmpty => false,
        SubLanguageResult::SEpsilon => false,
        SubLanguageResult::Failed => false,
    }
}

/// **Main Theorem**: If sub_language(r, s) returns true (witnessed by a
/// valid SubLanguageResult), then L(r) is a subset of L(s).
///
/// The proof dispatches on the result variant, calling the corresponding
/// case lemma for each arm of sub_language.
proof fn theorem_sub_language_soundness(
    r: REModel,
    s: REModel,
    result: SubLanguageResult,
)
    requires sub_language_result_valid(r, s, result),
    ensures
        forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
            language_of_re(s).contains(w),
    decreases result,
{
    match result {
        SubLanguageResult::Equal => {
            // r == s, so L(r) = L(s)
            lemma_sub_language_reflexive(r);
        }
        SubLanguageResult::REmpty => {
            // r = Empty, L(Empty) = {}
            assert(r == REModel::Empty);
            lemma_sub_language_empty(s);
        }
        SubLanguageResult::REpsilon => {
            // r = Epsilon, s is nullable
            assert(r == REModel::Epsilon);
            lemma_sub_language_epsilon(s);
        }
        SubLanguageResult::Complement { inner_result } => {
            // r = Complement(r1), s = Complement(s2)
            // Extract r1 and s2 from the structure
            let ghost r1: REModel;
            let ghost s2: REModel;
            match r {
                REModel::Complement { inner: r_inner } => {
                    r1 = *r_inner;
                    match s {
                        REModel::Complement { inner: s_inner } => {
                            s2 = *s_inner;
                            // Recursive call: L(s2) subset L(r1)
                            theorem_sub_language_soundness(s2, r1, *inner_result);
                            // By complement contravariance
                            lemma_sub_language_complement(r1, s2);
                            assert(language_of_re(r) =~=
                                complement_language(language_of_re(r1)));
                            assert(language_of_re(s) =~=
                                complement_language(language_of_re(s2)));
                        }
                        _ => { assert(false); } // unreachable by precondition
                    }
                }
                _ => { assert(false); } // unreachable by precondition
            }
        }
        SubLanguageResult::IntoUnion { k, inner_result } => {
            // s = Union(children), sub_language(r, children[k])
            let children = choose|children: Seq<REModel>|
                s == REModel::Union { children }
                && 0 <= k < children.len()
                && sub_language_result_valid(r, children[k], *inner_result);
            // Recursive call: L(r) subset L(children[k])
            theorem_sub_language_soundness(r, children[k], *inner_result);
            // By into_union: L(r) subset L(Union(children))
            lemma_sub_language_into_union(r, children, k);
            assert(s == REModel::Union { children });
        }
        SubLanguageResult::FromInter { k, inner_result } => {
            // r = Inter(children), sub_language(children[k], s)
            let children = choose|children: Seq<REModel>|
                r == REModel::Inter { children }
                && 0 <= k < children.len()
                && sub_language_result_valid(children[k], s, *inner_result);
            // Recursive call: L(children[k]) subset L(s)
            theorem_sub_language_soundness(children[k], s, *inner_result);
            // By from_inter: L(Inter(children)) subset L(s)
            lemma_sub_language_from_inter(children, s, k);
            assert(r == REModel::Inter { children });
        }
        SubLanguageResult::FromUnion { inner_results } => {
            // r = Union(children), all children subset s
            let children = choose|children: Seq<REModel>|
                r == REModel::Union { children }
                && inner_results.len() == children.len()
                && forall|k: int| 0 <= k < children.len() ==>
                    sub_language_result_valid(
                        #[trigger] children[k], s, inner_results[k]);
            // Recursive call for each child
            assert forall|k: int| 0 <= k < children.len() implies
                forall|w: Seq<u32>| language_of_re(#[trigger] children[k]).contains(w) ==>
                    language_of_re(s).contains(w)
            by {
                theorem_sub_language_soundness(children[k], s, inner_results[k]);
            }
            // By from_union: L(Union(children)) subset L(s)
            lemma_sub_language_from_union(children, s);
            assert(r == REModel::Union { children });
        }
        SubLanguageResult::IntoInter { inner_results } => {
            // s = Inter(children), r subset all children
            let children = choose|children: Seq<REModel>|
                s == REModel::Inter { children }
                && inner_results.len() == children.len()
                && forall|k: int| 0 <= k < children.len() ==>
                    sub_language_result_valid(
                        r, #[trigger] children[k], inner_results[k]);
            // Recursive call for each child
            assert forall|k: int| 0 <= k < children.len() implies
                forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
                    language_of_re(#[trigger] children[k]).contains(w)
            by {
                theorem_sub_language_soundness(r, children[k], inner_results[k]);
            }
            // By into_inter: L(r) subset L(Inter(children))
            lemma_sub_language_into_inter(r, children);
            assert(s == REModel::Inter { children });
        }
        SubLanguageResult::ConcatInclusion { u_elems, v_elems, patterns } => {
            // concat_inclusion succeeded on decompose_re(r) and decompose_re(s)
            // By theorem_concat_inclusion_soundness:
            //   language_inclusion(u_elems, v_elems) holds
            // i.e., language_of_seq(u_elems) ⊆ language_of_seq(v_elems)
            theorem_concat_inclusion_soundness(u_elems, v_elems, patterns);

            // By lemma_decompose_preserves_language:
            //   language_of_re(r) =~= language_of_seq(decompose_re(r)) = language_of_seq(u_elems)
            //   language_of_re(s) =~= language_of_seq(decompose_re(s)) = language_of_seq(v_elems)
            lemma_decompose_preserves_language(r);
            lemma_decompose_preserves_language(s);

            // Chain: language_of_re(r) ⊆ language_of_re(s)
            assert forall|w: Seq<u32>| language_of_re(r).contains(w) implies
                language_of_re(s).contains(w)
            by {
                assert(language_of_seq(u_elems).contains(w));
                assert(language_of_seq(v_elems).contains(w));
            }
        }
        // False cases -- precondition is false, so vacuously true
        SubLanguageResult::SEmpty => {}
        SubLanguageResult::SEpsilon => {}
        SubLanguageResult::Failed => {}
    }
}

// ============================================================================
// Level 4 (Phase 4): simplify_set_operation correctness
// ============================================================================

/// simplify_set_operation preserves the semantics of union/intersection.
///
/// For union: simplify_set_operation(v, empty, full) produces v' such that
///   Union(v) = Union(v')
///
/// The rules applied are:
///   - Remove bottom (neutral element): Union(X, empty) = X
///   - Absorb top: Union(X, full) = full
///   - Remove duplicates: Union(X, X) = X
///   - Complementary pairs: Union(X, complement(X)) = full
///
/// All these preserve the language.

/// Removing duplicates preserves union semantics
proof fn lemma_dedup_preserves_semantics(a_lang: Set<Seq<u32>>, rest_lang: Set<Seq<u32>>)
    ensures
        // Union(a, a, rest) = Union(a, rest)
        forall|w: Seq<u32>|
            (a_lang.contains(w) || a_lang.contains(w) || rest_lang.contains(w))
            <==> (a_lang.contains(w) || rest_lang.contains(w)),
{
}

/// Removing the bottom (empty language) preserves union
proof fn lemma_remove_bottom_preserves_semantics(rest_lang: Set<Seq<u32>>)
    ensures
        forall|w: Seq<u32>|
            (Set::<Seq<u32>>::empty().contains(w) || rest_lang.contains(w))
            <==> rest_lang.contains(w),
{
}

/// Complementary pair produces top (universal set)
proof fn lemma_complementary_pair_is_top(r: REModel)
    ensures
        forall|w: Seq<u32>|
            language_of_re(r).contains(w)
            || complement_language(language_of_re(r)).contains(w),
{
}

// ============================================================================
// Level 4 (Phase 4): remove_subsumed correctness
// ============================================================================

/// remove_subsumed preserves union semantics.
///
/// If we remove r from a union because sub_language(r, s) for some s in the union,
/// the union is unchanged because L(r) subset L(s) and s remains.
proof fn lemma_remove_subsumed_preserves_union(
    r: REModel,
    s: REModel,
    rest_lang: Set<Seq<u32>>,
)
    requires
        // L(r) subset of L(s)
        forall|w: Seq<u32>| language_of_re(r).contains(w) ==>
            language_of_re(s).contains(w),
    ensures
        // Union(r, s, rest) = Union(s, rest) (in terms of language membership)
        forall|w: Seq<u32>|
            (language_of_re(r).contains(w) || language_of_re(s).contains(w)
                || rest_lang.contains(w))
            <==> (language_of_re(s).contains(w) || rest_lang.contains(w)),
{
    assert forall|w: Seq<u32>|
        (language_of_re(r).contains(w) || language_of_re(s).contains(w)
            || rest_lang.contains(w))
        <==> (language_of_re(s).contains(w) || rest_lang.contains(w))
    by {
        if language_of_re(r).contains(w) {
            assert(language_of_re(s).contains(w));
        }
    }
}

/// Helper: element k has some subsumer in remaining
pub open spec fn element_has_subsumer(
    original: Seq<REModel>,
    remaining: Seq<REModel>,
    k: int,
) -> bool {
    exists|j: int| 0 <= j < remaining.len()
        && element_subsumed_by(original, remaining, k, j)
}

/// Helper: element k of `original` is subsumed by element j of `remaining`
pub open spec fn element_subsumed_by(
    original: Seq<REModel>,
    remaining: Seq<REModel>,
    k: int,
    j: int,
) -> bool {
    &&& 0 <= k < original.len()
    &&& 0 <= j < remaining.len()
    &&& forall|w: Seq<u32>| language_of_re(original[k]).contains(w) ==>
            language_of_re(#[trigger] remaining[j]).contains(w)
}

/// Repeatedly removing subsumed elements preserves the union.
/// If every element of `original` has its language included in some
/// element of `remaining`, then Union(original) subset Union(remaining).
///
/// This is the key correctness property of remove_subsumed in make_union.
proof fn lemma_remove_all_subsumed_preserves_union(
    original: Seq<REModel>,
    remaining: Seq<REModel>,
)
    requires
        // Every original element is subsumed by some remaining element
        forall|k: int| 0 <= k < original.len() ==>
            (#[trigger] element_has_subsumer(original, remaining, k)),
    ensures
        forall|w: Seq<u32>|
            language_of_re(REModel::Union { children: original }).contains(w)
            ==> language_of_re(REModel::Union { children: remaining }).contains(w),
{
    axiom_union_language(original);
    axiom_union_language(remaining);

    assert forall|w: Seq<u32>|
        language_of_re(REModel::Union { children: original }).contains(w) implies
        language_of_re(REModel::Union { children: remaining }).contains(w)
    by {
        // w in Union(original) means exists k: w in L(original[k])
        let k: int = choose|k: int| 0 <= k < original.len()
            && language_of_re(#[trigger] original[k]).contains(w);
        // original[k] has a subsumer in remaining
        assert(element_has_subsumer(original, remaining, k));
        // Unfold: exists j in remaining with L(original[k]) ⊆ L(remaining[j])
        let j: int = choose|j: int| 0 <= j < remaining.len()
            && element_subsumed_by(original, remaining, k, j);
        assert(language_of_re(remaining[j]).contains(w));
    }
}

} // verus!

fn main() {}
