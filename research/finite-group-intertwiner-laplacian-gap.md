---
rg: 2
id: finite-group-intertwiner-laplacian-gap
kind: claim
title: A fixed finite group has a multiplicity-independent intertwiner spectral gap
---

Fix a finite group `H` and a finite generating set `S`.  There is a constant

```text
kappa(H,S)>0
```

such that for every pair of finite-dimensional unitary representations
`rho:H->U(W)` and `sigma:H->U(V)`, the quadratic form

```text
E_(rho,sigma)(T)
  = sum_(s in S) ||rho(s)T-T sigma(s)||_2^2             (FIL1)
```

has kernel exactly `Hom_H(V,W)`, and every vector orthogonal to that kernel
satisfies

```text
E_(rho,sigma)(T) >= kappa(H,S) ||T||_2^2.               (FIL2)
```

The constant is independent of `dim V`, `dim W`, and all isotypic
multiplicities.  Consequently, for every threshold

```text
0 <= a < kappa(H,S),
```

the spectral low-energy space of the intertwiner Laplacian is **exactly**
`Hom_H(V,W)`.

Thus a spectral cutoff tending to zero cannot create new sub-block geometry
inside a fixed finite-group intertwining problem: below one uniform positive
scale it sees only the exact semisimple intertwiner space.
