---
rg: 2
id: odd-subset-relaxation-needs-local-extendability-proof
kind: route
title: Verify the three-context counterexample by direct evaluation
target: odd-subset-relaxation-needs-local-extendability
requires: []
---

Finite verification of the displayed counterexample.

*Consistent tuples.*  `C_2` forces `u = w` and `C_3` forces `v = w`, so a
consistent tuple has `u = v = w`; `C_1` allows both `000` and `111`.

*Honest satisfaction.*  For `x = 000`: `phi_1(0,0) = +1`, `a_(C_2,+1) =
a_(C_3,+1) = +1`, product `+1 = J^0`.  For `x = 111`: `phi_1(1,1) = +1`,
product `+1`.  So every honest encoding of every solution (and of every
consistent tuple, which are the same here) satisfies the constraint.

*Odd subsets and marginals.*  `|T_(C_1)| = 3`, `|T_(C_2)| = |T_(C_3)| = 1`,
all odd.  Marginal on `u` (shared by `C_1, C_2`): the `u`-coordinates of
`T_(C_1)` are `0, 0, 1`, giving `psi(0)^2 psi(1) = psi(1)` for every
`psi : {0,1} -> {+1,-1}`; the `u`-coordinate of `T_(C_2)` is `1`, giving
`psi(1)`.  Marginal on `v` (shared by `C_1, C_3`): coordinates `0, 1, 0`
give `psi(1)`; `T_(C_3)` gives `psi(1)`.  Marginal on `w` (shared by
`C_2, C_3`): `psi(1)` on both sides.  All consistent.

*Violation.*  `a_(C_1,phi_1) = phi_1(0,0) phi_1(0,1) phi_1(1,0) = (+1)(-1)(+1) = -1`,
`a_(C_2,+1) = a_(C_3,+1) = +1`; the product is `-1 != +1 = J^0`.

*Diagnosis.*  `(0,1) in S_(C_1)` lies in no consistent tuple, so honest
satisfaction never evaluates `phi_1` there and the route's factorization
step has no force at that point.  This is the local-extendability
hypothesis named in the claim.
