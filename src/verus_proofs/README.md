# Verus Proofs

Formal verification proofs for algorithms in rust-smt-strings using
[Verus](https://github.com/verus-lang/verus).

## Proof Files

| File | What it verifies | Verified / Axioms |
|------|-----------------|-------------------|
| `subsumption_proofs.rs` | Soundness of `sub_language` and `concat_inclusion` in `regular_expressions.rs` (lines 590-949) | 96 verified, 4 axioms |

## How to Run

### Prerequisites

- [Verus](https://github.com/verus-lang/verus) built from source
- Z3 4.12.5+ (installed via `pip install z3-solver==4.12.5.0` or from source)
- Rust toolchain compatible with Verus (see
  [Verus install instructions](https://github.com/verus-lang/verus/blob/main/INSTALL.md))

### Install Verus

```bash
git clone https://github.com/verus-lang/verus.git
cd verus/source
# Follow build instructions at https://github.com/verus-lang/verus/blob/main/INSTALL.md
./tools/get-z3.sh    # or install Z3 separately
cargo build --release
# Optionally add to PATH:
# ln -s $(pwd)/target-verus/release/verus ~/.cargo/bin/verus
```

### Verify

```bash
# From the repository root, verify a specific proof file:
verus src/verus_proofs/subsumption_proofs.rs

# Expected output:
# verification results:: 96 verified, 0 errors

# To suppress trigger warnings:
verus --triggers-mode silent src/verus_proofs/subsumption_proofs.rs
```

Each proof file is standalone and does not import or depend on other crate
source files. Proof files define their own spec models of the data structures
and algorithms they verify. This means verification runs independently of
`cargo build`.

## Subsumption Proofs (`subsumption_proofs.rs`)

### What is Verified

The proof establishes **soundness** of the `sub_language` and `concat_inclusion`
functions: if they return true, then the language inclusion L(r) ⊆ L(s) holds.

- **96 verified items**, 0 errors, 0 `assume()` statements
- **92 machine-checked** by Z3, **4 semantic axioms** (standard definitions of
  Union, Intersection, Kleene star, and a type-level bridge)
- Two main theorems:
  - `theorem_sub_language_soundness` — top-level soundness
  - `theorem_concat_inclusion_soundness` — core pattern-matching algorithm

### Proof Structure

```
Level 0 (Leaf)        CharSet covers, match_char_set, BasePattern ops
    |
Level 1 (Build)       base_patterns construction, char_sets_of_pattern, flatten_concat
    |
Level 2 (Match)       rigid_match_at, next/prev_rigid_match, prefix/suffix match
    |
Level 3 (Orchestrate) find_rigid_matches, set_flexible_regions, match_flexible_patterns
    |
Level 4 (Top)         concat_inclusion soundness, sub_language soundness
```

### Trust Model

The 4 remaining axioms (`#[verifier::external_body]`) are standard semantic
definitions that cannot be expressed as concrete Verus spec functions due to
limitations in structural decreasing over `Seq` types:

1. `axiom_union_language` — L(Union) = union of child languages
2. `axiom_inter_language` — L(Inter) = intersection of child languages
3. `lemma_full_element_universal` — Sigma* accepts all strings
4. `axiom_leaf_re_language` — RE-level and element-level semantics agree

All algorithmic correctness (pattern matching, charset coverage, segment
composition) is fully machine-checked.
