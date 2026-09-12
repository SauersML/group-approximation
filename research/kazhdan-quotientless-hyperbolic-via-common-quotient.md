---
rg: 2
id: kazhdan-quotientless-hyperbolic-via-common-quotient
kind: route
title: Add property (T) to a finite-quotient-free hyperbolic group through a common hyperbolic quotient
target: kazhdan-hyperbolic-group-without-finite-quotients
requires:
  - hyperbolic-group-without-finite-quotients
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - olshanskii-g-subgroup-quotient-theorem
---

Steps (2) => (3) of `hyperbolic-rf-question-equals-non-mf-question-proof`:
divide the finite-quotient-free group `G_0` by its finite radical, take the free
product `G_1 * K` with a torsion-free hyperbolic Kazhdan partner `K`, check
that both factors are Olshanskii G-subgroups (all finite radicals are
trivial), and take a non-elementary hyperbolic quotient `Q` onto which both
factors surject.  `Q` inherits property (T) from `K` and the absence of finite
quotients from `G_1`.

Hull's common-quotient theorem (`common-quotient-onto-normal-subgroup`) cannot
replace Olshanskii's here: its quotients are only acylindrically hyperbolic,
and word-hyperbolicity is the whole point of the target.
