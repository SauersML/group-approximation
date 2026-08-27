---
rg: 2
id: s3-reset-plane-selector-polarization-proof
kind: route
title: Use the invariant alternating form to Fourier-swap the reset plane
target: s3-reset-plane-has-common-invariant-selector-polarization
requires:
  - fanizza-schur-menu-has-common-codimension-one-residual
  - affine-selector-clifford-residual-packet
---

Every element of `GL_2(F_2)` preserves the unique nonzero alternating form
`Omega`.  Hence

```text
Omega g^(-T)=g Omega.                                   (SRP5)
```

Equation `(SRP5)` says that the identification `A^*->A` given by `Omega` is
`H`-equivariant.  Direct substitution in the standard selector symplectic
form shows that `(x,z)->(Omega z,Omega x)` preserves it; in characteristic
two no minus sign is needed.  Thus `(SRP3)` is an `H`-centralizing symplectic
map.  Witt/Clifford surjectivity implements it by a selector Clifford.  The
Lagrangian and full-character dimension assertions follow immediately, and
the inert dummy pair remains orthogonal throughout.
