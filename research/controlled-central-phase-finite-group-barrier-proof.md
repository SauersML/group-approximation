---
rg: 2
id: controlled-central-phase-finite-group-barrier-proof
kind: route
title: Induce characters of the enlarged center and test the restriction kernel
target: controlled-central-phase-finite-group-barrier
requires: []
---

Put `C=<D,c><=Z(H)`.  Every character `psi in C^` occurs in an irreducible
constituent of `Ind_C^H psi`; centrality of `C` makes that constituent retain
the scalar character `psi` on all of `C`.

If `c` is not in `D`, the restriction map

```text
C^ -> D^
```

has a nontrivial kernel character which is trivial on `D` and sends `c` to
`-1`.  Multiplying any extension of a selector character `x` by this kernel
character produces two characters of `C` with the same restriction to `D`
and opposite values on `c`.  Inducing both gives irreducible `H`
representations contradicting the uniqueness in `(NCG1)`.  Hence `c in D`.

Write `c=product_i z_i^(a_i)`.  On the selector character `x`, its scalar is
the corresponding character monomial

```text
(-1)^(a_0+sum_i a_i x_i),
```

where `a_0` records the chosen sign convention.  Comparing with `(NCG1)`
shows that `f` is affine on the Boolean cube.
