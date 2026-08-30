---
rg: 2
id: minimal-cantor-decomposition-rank-one-proof
kind: route
title: Combine dynamic asymptotic dimension, quasidiagonal traces, and a positive-entropy strictly ergodic model
target: minimal-cantor-crossed-products-have-decomposition-rank-one
requires: []
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Put `A = C(X) ⋊_alpha Z`.  A minimal homeomorphism of the infinite
Cantor set is free.  Hence `A` is separable, simple, unital, nuclear and
stably finite.  Guentner--Willett--Yu, *Dynamic asymptotic dimension:
relation to dynamics, topology, coarse geometry, and C*-algebras*,
Theorem 3.1 and Corollary 8.25, give

`dim_nuc(A) <= 2 dim(X) + 1 = 1`.                              `(MCP1)`

The crossed product is in the UCT class (equivalently, use Tu's theorem
for the amenable transformation groupoid).  Every trace on the simple
algebra `A` is faithful, so Tikuisis--White--Winter's quasidiagonality
theorem makes every trace on `A` quasidiagonal.  Finite nuclear dimension
implies `Z`-stability here, and Castillejos--Evington--Tikuisis--White--
Winter, *Nuclear dimension of simple C*-algebras*, Theorems A and B, now
give

`dr(A) <= 1`.                                                  `(MCP2)`

This upper bound is sharp.  The Pimsner--Voiculescu exact sequence gives

`K_1(A) = ker(id - alpha_* : C(X,Z) -> C(X,Z)) = Z`,           `(MCP3)`

because a continuous integer-valued invariant function is constant under
a minimal homeomorphism.  Since an AF algebra has zero `K_1`, `A` is not
AF.  Decomposition rank zero is equivalent to being AF, so `(MCP2)` and
`(MCP3)` prove `(MCD1)`.

For the entropy assertion, Downarowicz--Serafin, *A strictly ergodic,
positive entropy subshift uniformly uncorrelated to the Moebius function*,
Theorem 2.2, construct strictly ergodic subshifts of positive entropy
(indeed entropy arbitrarily close to `log N` on `N` symbols).  If their
one-sided convention is used, pass to the natural two-sided extension;
minimality, unique ergodicity and entropy are preserved.  The resulting
infinite minimal two-sided subshift is a Cantor set, its shift is a
homeomorphism, and `(MCD1)` applies.  Traces on a free minimal
transformation crossed product correspond to invariant probability
measures, so strict ergodicity also gives the uniquely traced assertion.
