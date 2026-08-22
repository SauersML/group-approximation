---
rg: 2
id: finite-rational-rank-flow-density-proof
kind: route
title: Approximate inside the minimal face of a rational stationary polytope
target: finite-rational-rank-flows-are-fd-dense
requires: []
---

For a simple packet type of dimension `d_i`, encode its tracial multiplicity
by `x_i`, so its central block has trace `d_i x_i`.  Common dimension one is

```text
sum_i d_i x_i=1.                                               (RFDP1)
```

Restriction and induction multiplicities are integers.  Consequently all
conditions in `(RFD1)` define a polytope

```text
P={x in R^N: A x=b, Cx>=c, x>=0}                               (RFDP2)
```

with rational matrices and vectors.

Let `F` be the minimal face of `P` containing the given real point `x` in its
relative interior.  The affine hull of `F` is defined over `Q`: it is obtained
from `(RFDP2)` by turning the inequalities active on `F` into equalities.
Gaussian elimination over `Q` gives a rational base point and a rational
basis for its translation space.  Rational coefficients are dense in real
coefficients, so rational points in `relint(F)` are dense there.  Choose one
such `y` satisfying `(RFD2)`.  Membership in the same face preserves exactly
the zero coordinates of `x`, and relative-interior approximation preserves
all strict inequalities.

Choose a common denominator `D` for the coordinates of `y`.  Then
`n_i=D y_i` are nonnegative integers, `(RFDP1)` gives total dimension `D`,
and every integer branching equation remains exact after multiplication by
`D`.  Take `n_i` copies of each simple packet type.  Equal restricted
multiplicity vectors are unitarily isomorphic, so choose edge intertwiners.
This realizes the integral stationary flow.

Nothing in this construction controls products of the chosen intertwiners
around cycles.  Such products live in continuous multiplicity unitary groups
and are absent from `(RFDP2)`, proving the stated boundary.

