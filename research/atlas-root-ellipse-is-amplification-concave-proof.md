---
rg: 2
id: atlas-root-ellipse-is-amplification-concave-proof
kind: route
title: Expand the ellipse into positive geometric means and apply their concavity
target: atlas-root-ellipse-is-amplification-concave
requires:
  - atlas-a4-finite-quotient-escape-fence
---

Write `a_01=2`, `a_23=2`, and `a_30=4`.  Expanding `(ROOT-CONC-1)` gives

```text
F(e)
 = sum_i a_i^2 e_i
   +2 sum_(i<j) a_i a_j sqrt(e_i e_j)
   +sum_i a_i sqrt(e_i e_12)
   +e_12,                                               (ROOT-CONC-4)
```

where `i,j` range over `01,23,30`.  Every linear term is concave, and the
geometric mean `(u,v) -> sqrt(uv)` is concave on the nonnegative quadrant.
All coefficients in `(ROOT-CONC-4)` are nonnegative, so `F` is concave.
Every term has degree one in `e`, proving positive homogeneity.

For an orthogonal direct sum `U=direct_sum_j U_j`, normalized trace gives

```text
1-Re tau(V_U(t))
 =sum_j theta_j(1-Re tau_j(V_(U_j)(t))),
```

where `theta_j` is the dimension fraction of the `j`-th block.  Thus its
squared-energy vector is `sum_j theta_j e^(j)`, and concavity proves
`(ROOT-CONC-2)`.  External amplification leaves the vector unchanged.

Finally, the finite-quotient escape fence gives `F(e^(j))>=1` for every
nontrivial regular quotient block.  Summing with weights of total one proves
`(ROOT-CONC-3)`.  The binary vector supported only at `12` evaluates to one,
so no larger universal constant follows from the sole condition that each
binary block has at least one nonzero coordinate.

