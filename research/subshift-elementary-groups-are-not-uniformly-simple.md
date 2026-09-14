---
rg: 2
id: subshift-elementary-groups-are-not-uniformly-simple
kind: claim
title: The simple Kazhdan LEF groups EL_n(LC(X,F_2)⋊Z) are not uniformly simple
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift, `R = LC(X,F_2) ⋊_T Z`, `n ≥ 3`, and
`G = EL_n(R)`. Then `G` is not uniformly simple. There is no `M` such that, for every `g ≠ 1`, every element of `G`
is a product of at most `M` conjugates of `g` and `g^{-1}`.

**Quantitative form.** Let `V ≠ ∅` be clopen with `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`. Then `e_12(1)` is not a product
of fewer than `2w+1` conjugates of `e_12(e_V)^{±1}`. Such `V` exists for every `w`, because `T` has no periodic points.

**Mechanism.** The note's finite models `φ_ℓ: M_n(R) → M_{n m_ℓ}(F_2)` carry the rank. It is conjugation invariant
and subadditive on `A − I`. A transvection over a set with no returns up to `2w` has rank at most `m_ℓ/(2w+1)`,
while `e_12(1) − I` has rank `m_ℓ`.

So the invariant-measure structure of `X` gives unbounded conjugation lengths. In the limit these are the rank
functions of `measure-rank-functions-are-limits-of-periodic-word-models`, but the proof needs no measure theory.

**Scope.** The same argument applies to any group EL_n(R) with exact finite models in which root coefficients have
arbitrarily small normalized rank. Over `F_q` it applies to `EL_n/Z` with the same count.

**Novelty.** Not checked beyond a grep of main. Unbounded conjugation lengths from small supports are folklore for
full groups of measure-preserving systems. Gal–Gismatullin (uniform simplicity of groups with proximal actions) should
be checked before any claim of novelty.

Route: `subshift-elementary-groups-are-not-uniformly-simple-proof`.
