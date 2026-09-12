---
rg: 2
id: reversible-automata-over-integers-are-block-permutation-words
kind: claim
title: Every reversible cellular automaton over the integers is, after grouping cells into blocks, a translation composed with block permutations along two translated partitions
artifacts:
  - research/artifacts/partitioned-and-regrouped-formalizability-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**OPEN here, as an imported statement not read from source.** Let `A` be finite and `F` a bijective
automaton on `A^Z`. After grouping cells into blocks of a common length, `F` is a translation composed
with two block permutations, along two partitions of `Z` into intervals of a common length that are
translates of each other.

## Attempts

- **Source.** Kari, "Representation of reversible cellular automata with block permutations",
  Math. Systems Theory 29 (1996). The statement is recalled, not read verbatim here, and no established
  node depends on it.
- **Partition lemma, partly derived** (artifact, Section 5), for neighbourhoods `{0,1}` and inverse
  `{−1,0}`:
  - the local rule factors as `f(a, b) = h(rho(a), lambda(b))`;
  - `a -> (lambda(a), rho(a))` is injective.
  Not re-derived: the counting step `|A| = |L| |R|` that makes both maps bijective.
- **Radius reduction regroups.** Reducing a general radius to those neighbourhoods groups cells into
  blocks, i.e., passes to `mZ`. With identity tracks and `Z`-equivariant representatives no radius
  reduction is known.
