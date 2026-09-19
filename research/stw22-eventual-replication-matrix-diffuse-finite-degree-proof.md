---
rg: 2
id: stw22-eventual-replication-matrix-diffuse-finite-degree-proof
kind: route
title: Force matrix fibres into their stable codimension range and take the matrix-diffuse minimum
target: stw22-half-slack-all-factor-weighted-copy-finite-degree-fillings
requires:
  - stw22-matrix-weighted-copy-uniform-finite-degree-fillings
  - stw22-diffuse-weighted-copy-all-finite-sphere-fillings
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-all-factor-finite-dimensional-breakthrough-2026-08-31.md
---

Every finite factor is either a normalized matrix factor or a diffuse II1
factor.

In the diffuse case, (AFD-2) gives strict support slack. The all-finite-degree
diffuse theorem supplies global `j`-connectivity and the first radius in
(AFD-3).

In `M_n`, put `p=supp(a)`, `k=m rank(p)`, and `c=n-k`. The zero
weight gives a singleton. If `a` is nonzero, half slack gives

```text
k<=n/2,       c=n-k>=k=m rank(p)>=m>=ceil(j/2),          (AFD-4)
```

and hence `2c>=j`. The matrix finite-degree theorem therefore supplies
global `j`-connectivity and the second radius in (AFD-3). Taking the
minimum proves the top-degree local assertion.

For every `2<=ell<=j`, the same inequality gives `2c>=ell`; the
degree-`ell` matrix and diffuse moduli therefore apply. Combine their
finitely many minima with the established degree-zero and degree-one
all-factor moduli. This is one common `LC^0,...,LC^j` package for
the fixed `j`, so the family is equi-`LC^j`. No continuity of the
matrix/diffuse type stratum is used or asserted. The dependence of
`C_j` on `j` is retained throughout.
