---
rg: 2
id: cook-levin-rank-pressure-needs-common-reservoir-decoder-proof
kind: route
title: Apply rational branch pressure only after assuming typed common-carrier partial isometries
target: cook-levin-rank-pressure-needs-common-reservoir-decoder
requires:
  - gatewise-cook-levin-rank-is-baseline-plus-unsat
  - gram-branching-capacity-with-overlap
  - rational-supercritical-branch-certificate
  - strongly-connected-branching-gives-rational-pressure
---

Once the stated common-carrier partial isometries exist, their orthogonal
ranges and off-target leakage are exactly the hypotheses of the established
branch-capacity calculation, which yields `(CLP1)`.  Pairing `(CLP1)` with the
positive rational subeigenvector gives `(CLP2)`.  If `y.x>=c` and
`e_j<=C_j Def(U)`, then

```text
kappa c <= kappa(y.x)
        <= y.e
        <= Def(U) sum_j y_j C_j,
```

which is `(CLP3)`.  Strong connectivity plus a genuine branch provides the
rational certificate when it was not supplied separately.

The route is deliberately conditional at the occurrence interface.  Neither
`gatewise-cook-levin-rank-is-baseline-plus-unsat` nor any required capacity
claim constructs the common projections, typed branch maps, or a
dimension-independent decoder from normalized-HS local tests.  Therefore this
route does not establish a non-MF or nonhyperlinear group.
