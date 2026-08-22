---
rg: 2
id: two-cubic-carrier-intersection-proof
kind: route
title: Intersect the two rank-doubled three-cycle carriers
target: two-cubic-residual-carriers-recover-the-deleted-source
requires:
  - positive-fixed-corner-cubic-energy-charges-deleted-rank
---

For each `i`, the proof of
`positive-fixed-corner-cubic-energy-charges-deleted-rank` orthogonally
decomposes

```text
K_i=span(QH,(XU_i)QH,(XU_i)^2QH)
```

into three-dimensional cyclic spaces indexed by the eigenvectors of
`C=QXQ`.  The extended compressed involution agrees with `X` on `K_i^perp`,
so `ran(W_i-1)` lies in `K_i intersect PH`.  On every cyclic summand its two
nontrivial residual eigenvalues have total squared displacement `f(c)>0`.
Thus the residual has rank exactly two on that summand.  Since
`dim(K_i intersect PH)=2 rank(Q)`, equality `(TCR2)` follows.

For `q in QH`,

```text
P(XU_i)q=PXq,
```

because `U_iq=q`.  Hence `V=PXQH` is contained in both carriers.  Condition
`(TCR4)` now gives `(TCR5)`.  The quantitative statement is the usual
principal-angle identity: the nonzero spectrum of
`P_(Z_1)P_(Z_2)P_(Z_1)` consists of the squared principal cosines, with one
eigenvalue-one block exactly on the intersection.

