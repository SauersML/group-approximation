---
rg: 2
id: lxxiii-counterexample-via-homogeneous-tower
kind: route
title: Take the limit of an obstructed unital matrix bundle tower with unbounded rank
target: lxxiii-unital-counterexample-exists
requires:
  - unital-limit-full-square-zero-at-finite-stage
  - homogeneous-full-square-zero-is-nilpotent-section
  - unital-homogeneous-system-without-full-square-zero
---

Let `A` be the limit of the tower supplied by
`unital-homogeneous-system-without-full-square-zero`.

**No finite-dimensional representations.**  Let `pi:A->M_d` be a nonzero
finite-dimensional representation and pass to an irreducible summand, which is
unital on its space.  Composing with the unital map from the `j`-th stage gives
a unital representation of `Gamma(X_j, End E_j)` on `C^d`.  Every irreducible
representation of that algebra is a point evaluation onto `M_(N_j)`, so `N_j`
divides `d`.  Since `N_j -> infinity`, this is impossible.

**No full square-zero element.**  By
`homogeneous-full-square-zero-is-nilpotent-section` no stage contains a full
square-zero element, and by `unital-limit-full-square-zero-at-finite-stage`
neither does `A`.
