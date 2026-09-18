---
rg: 2
id: edge-split-flop-spine-elements-split-disconnectedly
kind: claim
title: The five-piece flop spine elements of the rank-three edge-split operad have splitting category homotopy equivalent to S^0, like a full split in two directions
distinct_from:
  thumann-finiteness-without-finite-type: that proves finite presentation of operad groups when large strictly elementary classes have connected splitting categories (condition (G)); this computes the splitting category of the smallest nontrivial spine elements of the edge-split operad, as the calibration for testing (G) there.
  edge-split-operad-satisfies-ore: that records the flop pairs as the minimal common upper bounds of two first splits and bounds the spine from below; this computes the splitting category of those elements.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). A finite hand computation. It has
not been independently reviewed, and no priority is claimed.

## Setting

- **The operad.** `m = 2` and `Δ = cone(e_0, e_1, e_2)`. `𝒪_E` is the edge-split
  operad, with classes taken modulo the symmetries of `Δ`.
- **The elements.** `F_±` are the two minimal common upper bounds of `E_{01}` and
  `E_{02}` (`edge-split-operad-satisfies-ore`, Attempt 1). They are spine elements,
  since the two maximal spine elements below them are `E_{01}` and `E_{02}`.
- **The splitting category.** `𝒜(Θ)` is the poset of proper elementary
  pre-factorizations of Thumann's proof, as defined in
  `thumann-finiteness-without-finite-type`. Here its elements are split trees `D'`
  with `Δ < D' <_E Θ` such that `Θ|_p` is a spine element or trivial on each piece
  `p`, and nontrivial on at least one. It is ordered by coarsening.

## Statement

`𝒜(F_±)` has exactly six elements, in two components, and each component is a
cone. So `𝒜(F_±) ≃ S^0`.

## Proof (for `F_+`, the diagonal `v_{01} — v_{02}`; `F_−` is the same with the other diagonal)

**The pieces.** Put `c = (1,1,1)`. The pieces of `F_+` are:
- `1 = cone(e_0, v_{01}, v_{02})`;
- `2 = cone(v_{01}, c, v_{02})`;
- `3 = cone(v_{01}, e_1, c)`;
- `4 = cone(v_{02}, c, e_2)`;
- `5 = cone(c, e_1, e_2)`.

**Mergeable pairs.** A single merge must produce a split tree below `F_+` whose
refinement to `F_+` is one split. The unions that are unimodular cells and give such a
split tree are:
- `2 ∪ 4 = cone(v_{02}, v_{01}, e_2)`;
- `3 ∪ 5 = cone(v_{01}, e_1, e_2)`;
- `2 ∪ 3 = cone(v_{01}, e_1, v_{02})`;
- `4 ∪ 5 = cone(v_{02}, e_1, e_2)`.

The unions `1 ∪ 2` (a quadrilateral), `3 ∪ 4` and the other pairs are not cells. The
four merges give the 4-piece elements:
- `a = {1, 24, 3, 5}`, which is `E_{01} ∘ (E, E)`;
- `b = {1, 2, 4, 35}`, which is `E_{01} ∘ (E∘(id, E), id)`;
- `c' = {1, 23, 4, 5}`, which is `E_{02} ∘ (E, E)`;
- `d = {1, 2, 3, 45}`, which is `E_{02} ∘ (E∘(id, E), id)`.

**Double merges.** Only two pairs of disjoint mergeable pairs exist. They give the
3-piece elements:
- `D'_1 = {1, 24, 35} = E_{01} ∘ (E, id)`, which lies below `a` and `b`;
- `D'_2 = {1, 23, 45} = E_{02} ∘ (E, id)`, which lies below `c'` and `d`.

**Nothing coarser.**
- The unions `1 ∪ 2 ∪ 4 = {x_1 ≤ x_0}` and `1 ∪ 2 ∪ 3 = {x_2 ≤ x_0}` are cells. But
  the restriction of `F_+` to each of them is a 3-piece path tree `E ∘ (E, id)`.
- That path tree is not a spine element: its only nontrivial spine element below is
  its first split, which is then the greatest one.
- So `{x_1 ≤ x_0} ∪ …` gives no element of `𝒜`, and neither do `E_{01}` and `E_{02}`
  themselves.

**Components.**
- The order relations are exactly `D'_1 < a, b` and `D'_2 < c', d`. The 4-piece elements
  are pairwise incomparable, and each 3-piece element coarsens only the two 4-piece
  elements that merge one of its pairs.
- The side containing `a`, `b` and `D'_1` is `≥_E E_{01}`, and every element there has a
  piece that straddles `x_0 = x_2`. Symmetrically, every element on the other side has
  a piece that straddles `x_0 = x_1`. ∎

## What this means for condition (G)

- **(G) in this operad.** By `thumann-finiteness-without-finite-type`, finite
  presentation of the edge-split group needs, besides Ore's condition, that
  `𝒜(Θ)` be connected for every spine element `Θ` of large degree.
- **The small case is harmless.** The degree-5 elements are disconnected, exactly as
  a full split in two directions is in Brin–Thompson groups. That is harmless at
  degree 5.
- **What the test for larger spine elements asks.** Whether spine elements of large
  degree keep this two-sided shape (only two maximal spine elements below, with no
  element of `𝒜` joining their sides), or have at least three overlapping sides, like
  full splits in at least three directions.
- **A warning.** Merging two disjoint mergeable blocks of a split tree need not give
  a split tree (compare `split-tree-restrictions-to-a-child-need-not-be-split-trees`).
  So the connections that make Brin–Thompson splitting categories spheres are not
  automatic here.

## Lesson for general BH

- **(G) is a local test.** For non-LCM dissection operads, condition (G) asks whether
  large spine elements have more than two "sides".
- **The smallest spine elements have exactly two sides.** The flop pairs are the
  minimal common upper bounds of two first splits, and their splitting category is
  `S^0`.
- **What decides finite presentation.** If every large spine element is again a
  two-sided minimal common upper bound, (G) fails and this route to finite
  presentation needs another tool. If large elements are many-sided, (G) holds.
- **Where to look.** The rank-three computation of splitting categories for the spine
  elements found by the reversing search (bh-free-54) decides it.
