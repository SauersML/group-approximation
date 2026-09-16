---
rg: 2
id: stw74-lxxiv-hinge-is-two-level-descent
kind: claim
title: For LXXIV algebras, property SP is equivalent to descent of projections from 2x2 matrices over hereditary subalgebras
distinct_from:
  stw74-property-sp-is-the-exact-missing-condition: that identifies pure infiniteness with property (SP) for LXXIV algebras; this replaces (SP) by the formally weaker single-level implication from M_2(H) to H, and gives a two-isometry form.
  stw74-counterexamples-have-stationary-matrix-thresholds: that finds some least matrix level m>=2 on a spectral tower and freezes it; this re-chooses the hereditary subalgebra inside the same algebra so that the failure occurs exactly at level 2.
  stw74-hypothesis-forces-property-sp: that is the open hole itself; this is an equivalence valid in every LXXIV algebra and does not decide either side.
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Let `A` be a unital simple C\*-algebra in which every nonzero projection is
infinite.  The following are equivalent.

1. `A` has property (SP).
2. For every hereditary C\*-subalgebra `H` of `A`: if `M_2(H)` contains a
   nonzero projection, then `H` contains a nonzero projection.
3. For every `a in A_+` and all `t_1,t_2 in A` with `t_i* t_j = delta_ij 1`:
   if `Her(t_1 a t_1* + t_2 a t_2*)` contains a nonzero projection, then so
   does `Her(a)`.
4. For some fixed pair `t_1,t_2` as in (3), the implication in (3) holds for
   every `a in A_+`.

Moreover, if `A` fails (SP) and `Her(a)` is projectionless with least matrix
projection level `m>=2`, then for any `t_1,t_2` as in (3) the element
`b=sum_(i<m) w_i a w_i*`, with `w_i=t_2^(i-1) t_1`, is nonzero, `Her(b)` has
no nonzero projection, and `M_2(Her(b))` contains one.

Thus the whole LXXIV hinge is the single level-two implication
"`M_2(H)` has a nonzero projection => `H` has one".
