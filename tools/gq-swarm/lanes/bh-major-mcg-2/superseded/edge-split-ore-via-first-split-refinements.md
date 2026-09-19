---
rg: 2
id: edge-split-ore-via-first-split-refinements
kind: route
title: Ore's condition for the edge-split operad follows from refining any edge-split dissection into one that splits first at a prescribed edge
target: edge-split-operad-has-common-refinements
requires:
  - edge-split-dissections-refine-into-any-first-split
---

Lane bh-major-mcg-2, 2026-09-18. Every rank `m ≥ 1`. Notation of
`edge-split-operad-satisfies-ore`. `GL_{m+1}(Z)` acts equivariantly on edge splits, so
statements about `Δ` hold in every unimodular cell.

**Claim.** For all cells `P` and all `X, Y ∈ 𝒪_E(P)`, there is `Z ∈ 𝒪_E(P)` with
`Z ≥_E X` and `Z ≥_E Y`.

**Proof by induction on `|Y|`, for all `X` and `P` at once.**
- **`|Y| = 1`.** `Z = X`.
- **`|Y| ≥ 2`.**
  - Write `Y = E_b ∘ (Y_1, Y_2)`, with `Y_i ∈ 𝒪_E(H_i)` on the halves of `E_b`, and
    `|Y_i| < |Y|`.
  - `edge-split-dissections-refine-into-any-first-split` gives `X' ≥_E X` with
    `X' ≥_E E_b`. So `X' = E_b ∘ (X'_1, X'_2)` with `X'_i ∈ 𝒪_E(H_i)`.
  - By the induction hypothesis in the cells `H_i` (with `X'_i` arbitrary), there are
    `Z_i ≥_E X'_i, Y_i`.
  - Then `Z = E_b ∘ (Z_1, Z_2)` satisfies `Z ≥_E X' ≥_E X` and `Z ≥_E Y`. ∎

**Converse.** The claim applied to `(D, E_b)` is the required input. So the input
and Ore's condition are equivalent.

This route replaces `edge-split-ore-via-atom-plane-restriction`, whose input is
refuted by `edge-split-respecting-a-split-plane-need-not-refine-it`.
