---
rg: 2
id: leavitt-two-compressor-permutation-model-proof
kind: route
title: Realize the two children by diagonal and coordinate translations on H times H
target: leavitt-two-compressor-covariance-triangle-has-marked-models
requires: []
---

Let a finite group `H` act on `X=H x H` by

```text
D_g(a,b)=(ga,gb),       L_g(a,b)=(ga,b),       R_g(a,b)=(a,gb).
```

Define permutations

```text
T_0(a,b)=(a,a^(-1)b),
W(a,b)=(b^(-1),ab^(-1)),
T_1=W T_0.
```

Direct substitution gives

```text
T_0 D_g T_0^(-1)=L_g,
W L_g W^(-1)=R_g,
W^3=1,
T_1 D_g T_1^(-1)=R_g,
T_1 T_0^(-1)=W.
```

The left and right coordinate actions commute.  Taking `H=Lambda_k` gives
the exact finite-depth two-compressor covariance table.  In the permutation
representation on `ell^2(X)`, a nonidentity involution `D_z` has only
two-cycles, so `-1` is an eigenvalue and `||D_z-1||=2`.  Letting the diagonal
stage grow yields the claimed marked finite-window models.
