---
rg: 2
id: thompson-f-p21-over-f2-every-pair-meets-in-degree-seven
kind: claim
title: Over F_2, every pair in Guba's Problem P_(2,1) for Thompson's F has a common right multiple of degree at most seven, and seven is attained
distinct_from:
  thompson-f-p21-cardinality-certificate-in-degree-eleven: that solves P_(2,1) over every field in degree eleven with one cardinality certificate; this computes the exact minimal degree of a common multiple for each of the 465 pairs over F_2, which is at most seven.
  thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9: that is a lower bound for one generic integer pair of P_(2,2) in characteristic 0; this is an exhaustive upper and lower bound for all pairs of P_(2,1) over F_2.
artifacts:
  - research/artifacts/thompson-f-ore-over-f2-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-p21-over-f2-degree-seven-exhaustive-proof` (exhaustive exact
computation with explicit certificates; not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, with normal forms `x_(i_1) ... x_(i_d)`, `i_1 <= ... <= i_d`, and
`S_(2,4) = {x_0^2, x_0x_1, x_0x_2, x_1^2, x_1x_2}`, the five monomials of Guba's Problem `P_(2,1)`
(V. Guba, arXiv:2305.07113v4).

1. For every two distinct nonzero `a, b ∈ F_2[S_(2,4)]` there are nonzero `u, v ∈ F_2[M]`, homogeneous
   of one degree `<= 7`, with `a u = b v`.
2. The exact minimal degree of such `u, v`, over the 465 pairs, is distributed as
   `{1: 45, 2: 138, 3: 84, 4: 90, 5: 69, 6: 27, 7: 12}`. In particular 12 pairs have no nonzero common
   right multiple of degree `<= 6`.

**Comparison.** Guba's Theorem `s24` gives solutions of degree `<= 41` over every field, and
`thompson-f-p21-cardinality-certificate-in-degree-eleven` gives `11` over every field and shows no
cardinality certificate exists below degree `11`. Over `F_2` actual common multiples appear by degree `7`.
So the cardinality method overshoots the true minimal degree for this problem.

**Scope.** Only `K = F_2`, and only `P_(2,1)`. This proves nothing about `thompson-f-is-amenable` or
`thompson-f-is-not-amenable`.
