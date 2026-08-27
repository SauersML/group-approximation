---
rg: 2
id: harris-maximal-matrix-range-proof
kind: route
title: Center the Harris diagonal and apply the maximal-matrix-range LP theorem
target: harris-lp-is-maximal-matrix-range-collapse
requires: []
---

Harris's formulas give

```text
D=diag(1,2,...,n+2)
```

and put a scalar `1` in the two off-diagonal blocks joining vertices `1`
and `n+2`.  Centering `D` at `c=(n+3)/2` therefore produces the four scalar
matrix-range points in `(HMR3)`.  Their convex hull has nonempty interior
around zero.  Passer--Paulsen Theorem 3.3 applies to the centered
self-adjoint pair and identifies LP with `gamma(T)=1` and uniform
maximal-hull convergence; their Corollary 3.4 gives the free-spectrahedral
formulation.  The basis-free `d_k` formulation is Aubrun et al. Theorem 6.1.
