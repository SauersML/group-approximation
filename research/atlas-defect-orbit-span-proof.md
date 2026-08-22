---
rg: 2
id: atlas-defect-orbit-span-proof
kind: route
title: Quotient by the normal residual image and use simplicity of the natural A8 module
target: atlas-defect-orbit-span-quotient-dichotomy
requires:
  - atlas-repeated-h6-gauge-is-one-gl2m-coordinate
  - atlas-exact-matrix-zero-set-is-a-finite-quotient-test
---

By construction, `W(rho)` is invariant under both free factors and hence
under `A8*A8`.  For every defining relator `r` and every `v in E`,

```text
(rho(r)-I)v in D(rho) subset W(rho).
```

Therefore every `r` acts trivially on `E/W(rho)`, so the quotient
representation factors through `Gamma_+`.

It remains to check the marked chart type.  The natural
`GL_4(F2)`-module `V` is simple: a nonzero invariant subspace is invariant
under all invertible elementary transvections and hence contains every basis
direction.  The module `V^m` is semisimple, so every submodule and quotient
is a direct sum of copies of `V`.  Since `W(rho)` is invariant under each
chart separately, a nonzero quotient `E/W(rho)` restricts to `V^k` for the
first chart and to `V^ell` for the second.  Equality of the underlying
dimension gives `k=ell>0`.  Each restriction is faithful because `V` is
faithful.  This proves `(DOS2)`.

The contrapositive gives `(DOS3)`.  Subadditivity of dimension gives

```text
dim W_d(rho)<=|B_d(A8*A8)| dim D(rho),
```

so uniform saturation gives `(DOS7)` and `(DOS6)`.  More generally `(DOS5)`
alone makes the quotient nonzero eventually and completes the same exact
finite-model extraction.  No stability theorem is used: all loss is isolated
in the possible growth from `D(rho)` to its full alternating orbit-span.

