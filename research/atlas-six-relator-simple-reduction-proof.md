---
rg: 2
id: atlas-six-relator-simple-reduction-proof
kind: route
title: Pass every finite six-relator escape to a bridge-retaining maximal simple quotient
target: atlas-six-relator-finite-escape-is-simple-test
requires:
  - atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test
  - atlas-six-relator-natural-orbit-mixing-floor
  - atlas-19243-centrality-forces-s3-distance
  - atlas-boundary-tangent-covariance-coercivity
---

Take a nontrivial finite quotient and then a maximal proper normal quotient.
The chart kernels are normal in simple `A8`.  The exact one-chart evaluations
in `atlas-six-relator-natural-orbit-mixing-floor` exclude exactly one trivial
chart, while generation excludes two trivial charts.  Both chart copies
therefore inject into the resulting nonabelian simple quotient.

If their labelled `H=GL3(2)` copies agreed, the regular relative frame would
commute with `K_19243<S3`.  The exact constant value underlying
`atlas-19243-centrality-forces-s3-distance` then makes `c_19243` a fixed
nonidentity commutator, contradicting the sixth relation.  Thus an `H`
bridge survives.  Boundary tangent coercivity turns that bridge into
positive five-row linear energy, and the established finite-quotient
criterion supplies the equivalence with an exact finite-dimensional escape.

Finally the simple quotient cannot equal `A8`: the complete inner/outer
alignment audit has no six-relator survivor.  This proves the target.

