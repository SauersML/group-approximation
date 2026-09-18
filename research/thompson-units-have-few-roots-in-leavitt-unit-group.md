---
rg: 2
id: thompson-units-have-few-roots-in-leavitt-unit-group
kind: claim
title: In the binary Leavitt unit group a conjugate of an infinite-order Thompson unit has k-th roots only for k dividing its centralizer rank, and the north-south unit has no proper root
distinct_from:
  thompson-elements-are-undistorted-in-leavitt-unit-group: that excludes power conjugates of Thompson units through depth growth; this excludes roots of large order, which distortion estimates do not control, since roots of an undistorted element are undistorted.
  leavitt-thompson-units-have-finite-centralizer-rank: that bounds the centralizer rank; this converts the bound into a bound on the orders of roots.
  unit-roots-divide-centralizer-rank: that is the general divisibility lemma; this is its consequence for Thompson units in L_(F_2)(1,2).
---

**ESTABLISHED** (proof: `thompson-units-have-few-roots-in-leavitt-unit-group-proof`). Not independently
reviewed.

Let `R = L_(F_2)(1,2)` and `U = R^x`. For `g in V` write `u_g` for its Thompson unit, as in
`leavitt-thompson-units-have-finite-centralizer-rank`, with the bound `N(g)` defined there.

1. Let `g in V` have infinite order, `w in U`, and `y = w u_g w^(-1)`. If `y = z^k` for some `z in R` and
   `k >= 1`, then `k` divides `rho(y)`, so `k <= rho(y) <= min(N(g), N(g^(-1)))`. In particular `y` has
   `k`-th roots in `U` for only finitely many `k`.
2. The north--south unit `c` and all its conjugates in `U` have no `k`-th root in `R` for any `k >= 2`.
3. So no conjugate of an infinite-order Thompson unit is a nonzero element of a subgroup `(Q,+)` or `Z[1/p]`
   of `U`. So a copy of `(Q,+)` in `U`, and the unipotent subgroup `(Q,+)` of any copy of `Aff(Q)` or of
   `GL_n(Q)` (`n >= 2`) in `U`, meets the conjugates of the infinite-order Thompson units only in `1`: it has to
   be built from genuinely linear units.

This extends to the whole Leavitt unit group Higman's theorem that an infinite-order element of `V` has
`k`-th roots in `V` for only finitely many `k` (survey arXiv:2306.16356v3, sketch of Theorem 4.4).
