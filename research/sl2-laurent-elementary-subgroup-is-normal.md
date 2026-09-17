---
rg: 2
id: sl2-laurent-elementary-subgroup-is-normal
kind: claim
title: "E_2(Z[t,t^-1]) is normal in SL_2(Z[t,t^-1])"
distinct_from:
  sl2-laurent-integers-equals-elementary-subgroup: that asks for equality; this asks only for normality, which is necessary for equality but a priori weaker.
---

The elementary subgroup `E_2(R)`, `R = Z[t,t^{-1}]`, is normal in `SL_2(R)`.

By item 2 of `sl2-laurent-elementary-iff-three-unipotent-conditions`, this is
equivalent to: for every unimodular pair `(p,q)` (`pR + qR = R`), the Cohn matrix
`C(p,q) = [[1+pq, p^2],[-q^2, 1-pq]]` is a product of elementary matrices.
Equivalently, every `SL_2(R)`-conjugate of `E_12(1)` is elementary.

This is condition (N) of the three-way split of
`sl2-laurent-integers-equals-elementary-subgroup`. For `n ≥ 3`, `E_n(A)` is normal in
`SL_n(A)` for every commutative ring `A` (Suslin's normality theorem); nothing of the
kind is available for `n = 2`.

## Attempts

- **Trivial instances are exactly the reducible rows.** Let `w = (p,-q)^T` be
  unimodular with `w = Y e_1 · u` for some `Y ∈ E_2(R)` and a unit `u`, i.e. `w` is
  reducible to a unit multiple of `e_1` by elementary operations. Then by item 5 of
  the split, `C(w)` is `E_2`-conjugate to `C(u,0) = E_12(u^2)`, which is elementary.
  So a nontrivial instance of (N) needs a unimodular row that is not
  elementary-reducible, and that is precisely a counterexample to
  `sl2-laurent-integers-equals-elementary-subgroup`. Consequently (N) can fail only
  if the target fails, and every elementary reduction of a unimodular row (such as
  Cohn's `C(2,t)`, whose vector `(2,-t)` has a unit coordinate) is evidence for (N)
  only in this indirect sense. (N) is the residual question: at a hypothetical
  non-reducible unimodular `w`, is `C(w)` still elementary?
