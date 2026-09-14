---
rg: 2
id: thompson-f-p22-over-f2-exhaustive-degree-seven-census
kind: claim
title: Over F_2, exactly 94329 of the 130305 pairs in Guba's Problem P_(2,2) for Thompson's F have no nonzero common right multiple of degree at most seven
distinct_from:
  thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9: that bounds one explicit integer pair from below in characteristic 0 and over F_(2^61-1); this is an exhaustive count over F_2 for every pair, in both directions, up to degree seven.
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes cardinality ratios of the nine monomials, a method that can only solve all pairs at once; this computes, pair by pair, whether any common multiple exists.
  thompson-f-p21-over-f2-every-pair-meets-in-degree-seven: that settles every pair of P_(2,1) over F_2 by degree seven; this shows that for P_(2,2) most pairs are still unsettled at degree seven.
artifacts:
  - research/artifacts/thompson-f-ore-over-f2-2026-09-13.md
  - research/artifacts/thompson-f-ore-over-f2-2026-09-13-data/census_over_f2.json
  - research/artifacts/thompson-f-ore-over-f2-2026-09-13-data/s35_unsolved_after_k7.json.gz
---

**ESTABLISHED** through `thompson-f-p22-over-f2-census-exhaustive-proof` (exhaustive exact computation;
not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, and `S_(3,5)` the nine monomials of Guba's Problem `P_(2,2)`
(V. Guba, arXiv:2305.07113v4): `x_0^2, x_0x_1, x_0x_2, x_0x_3, x_1^2, x_1x_2, x_1x_3, x_2^2, x_2x_3`.
Consider all 130305 unordered pairs of distinct nonzero `a, b ∈ F_2[S_(3,5)]`. For each pair let `δ(a,b)`
be the least degree of nonzero homogeneous `u, v ∈ F_2[M]` with `a u = b v`, or `∞` if there are none.

1. The number of pairs with `δ = 1, 2, ..., 7` is `357, 3804, 3399, 6951, 5799, 7629, 8037`.
2. The remaining 94329 pairs have `δ > 7`: they have no nonzero common right multiple of degree `<= 7`.
   Their list is in `s35_unsolved_after_k7.json.gz`.

**Relation to the root.** By Guba's alternative (survey, after Problem `P_(d,m)`), a single pair with
`δ = ∞` over any field proves `thompson-f-is-not-amenable`, and `F` is amenable iff every `P_(d,m)` is
solvable over every field. Over `F_2`, `P_(2,2)` is the finite family above. Item 2 names the 94329 pairs
that remain candidates for a non-Ore pair after degree seven. It proves nothing about either root: a
finite computation only ever settles pairs positively.

**Growth.** Per-degree settled counts do not decay through degree seven (`5799` at degree 5, `7629` at 6,
`8037` at 7). By contrast every pair of `P_(2,1)` is settled by degree seven.
