---
rg: 2
id: edge-split-dissections-refine-into-any-first-split
kind: claim
title: Every edge-split dissection of a unimodular simplex cone has an edge-split refinement that also refines any prescribed first edge split
distinct_from:
  edge-split-dissections-respecting-an-atom-plane-split-there: that (LD_atom, refuted) asks for no refinement at all once the dissection respects the plane; this allows further splits of the pieces, which is exactly what the ten-piece counterexample needs.
  edge-split-operad-has-common-refinements: that is Ore's condition for all pairs; this is its special case where one member of the pair is a single first split, and the route edge-split-ore-via-first-split-refinements proves the two are equivalent.
  edge-split-operad-satisfies-ore: that bundles Ore's condition with a finite spine; this is only the Ore half, in its atomic form.
---

**OPEN** (lane bh-major-mcg-2, 2026-09-18). It is equivalent to Ore's condition for
`𝒪_E` (`edge-split-ore-via-first-split-refinements`). For `m = 1` it is trivial.

## Statement (WLD_m)

Notation of `edge-split-operad-satisfies-ore`.
- **Data.** A unimodular cell `P ⊂ R^{m+1}`, a dissection `D ∈ 𝒪_E(P)`, and a first
  split `E_b` of `P` (at an edge `b` of `P`).
- **Conclusion.** There is `D' ∈ 𝒪_E(P)` with `D' ≥_E D` and `D' ≥_E E_b`. That is, the
  pieces of `D` can be split further until the whole dissection splits at `b` first.

## Evidence and what is known

1. **The atom case is known** (`edge-split-operad-satisfies-ore`, Attempt 1): if `D`
   is itself a first split, a common upper bound with 5 pieces exists (a flop pair).
2. **The ten-piece example.**
   `edge-split-respecting-a-split-plane-need-not-refine-it` gives a `D`
   that respects the plane of `E_{01}` without refining `E_{01}`. Two more splits give a
   `D'` as required.
3. **Cutting is not enough.** By the cut lemma of
   `edge-splits-cut-every-rational-hyperplane`, every `D` has an edge-split refinement
   respecting the plane of `E_b`. By item 2, that refinement need not refine `E_b`.

## A sufficient decomposition (untested)

WLD for `(D, E_b)` would follow from two statements:
- **(a) Sync in split-tree form.** For a descendant `p` of `P` lying in a half `H` of
  `E_b`, some split tree of `p` has all its leaves in `Desc(H)`. The descent-set
  version is `unimodular-cells-synchronize-under-edge-splits`, reduced in
  `edge-split-sync-reduces-to-totally-irrational-shared-rays`.
- **(b) Split-tree completion.** A dissection of a cell `H` into descendants of `H`
  has a refinement, by split trees of its pieces, that is a split tree of `H`.

To apply them, cut `D` by the plane of `E_b`, use (a) in each piece, then use (b) in
each half. Neither statement is known. The counterexample above shows that (b) can
genuinely require refinement.

## Lesson for general BH

- **Ore's condition is atomic here.** For dissection operads, Ore's condition reduces
  to the case where one member of the pair is a single generator.
- **What the atomic case asks.** Every dissection can be refined into one that makes a
  prescribed first cut. This is the non-LCM analogue of "every element has a common
  multiple with each atom".
- **Why this is the right target.** Rearrangement (no refinement) is false. So a proof
  must build the refinement, for example through (a) and (b) above.
