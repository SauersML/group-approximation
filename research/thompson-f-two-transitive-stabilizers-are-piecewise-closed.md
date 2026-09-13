---
rg: 2
id: thompson-f-two-transitive-stabilizers-are-piecewise-closed
kind: claim
title: Point stabilizers of a 2-transitive action of Thompson's group F are closed under piecewise agreement
distinct_from:
  thompson-f-two-transitive-actions-satisfy-grid-condition: that claim gives the orbit grid and splitting at a single point; this claim assembles the splitting at all dyadic points into closure of the stabilizer under piecewise agreement with its own elements
---

Let `F` act 2-transitively on `Ω`, `|Ω| ≥ 3`, and let `H = F_ω`. If `g ∈ F`,
`0 = x_0 < x_1 < … < x_n = 1` are dyadic, and each restriction
`g|_[x_{i-1},x_i]` equals `h_i|_[x_{i-1},x_i]` for some `h_i ∈ H`, then
`g ∈ H`.

Equivalently, by compactness: `g ∈ H` as soon as every `t ∈ [0,1]` has a
neighborhood (one-sided at dyadic points is enough) on which `g` agrees with
some element of `H`. So `H` is determined by the germs of its elements. For
example, the stabilizer of any subset of `(0,1)` has this property, while the
stabilizer of a partition whose elements may swap the parts can fail it.

This is closedness in the sense of Golan–Sapir: `H = Cl(H)`, the subgroup of
all piecewise-`H` functions (arXiv:2105.00531v1, Definitions 1.2 and 1.3). It
is not new as a property of maximal subgroups. The introduction of
arXiv:2105.00531v1 records Golan's result that all maximal subgroups of `F` of
infinite index are closed, and `H` is maximal of infinite index by
`thompson-f-two-transitive-actions-are-faithful` and
`thompson-f-two-transitive-stabilizers-minimal-not-confined`. The proof here is
independent: it uses only the grid condition. So closedness gives no
contradiction by itself.

Unreviewed as of 2026-09-13.

**Proof:** `thompson-f-two-transitive-stabilizers-are-piecewise-closed-proof`.
