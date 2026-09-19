---
rg: 2
id: metaplectic-exact-finite-model-proof
kind: route
title: Detect the metaplectic centre in a finite quotient and cut its regular representation
target: metaplectic-half-class-has-an-exact-finite-model
requires: []
---

Let `E_infinity` be the arithmetic inverse image of `Sp_4(Z)` in the
universal cover of `Sp_4(R)`, with central deck group `Z<z>`.  Deligne's
finite-residual theorem says that its finite residual is `2Z`; equivalently,
the quotient `E_2=E_infinity/<z^2>` is residually finite.  One current source
is Stover, *Residual finiteness and discrete subgroups of Lie groups*,
arXiv:2407.07680v2, Theorem 1.5 and the sentence immediately following it.

The surviving central involution `z` is therefore nontrivial in some finite
quotient `F` of `E_2`.  In the left regular representation of `F`, the
`-1`-spectral subspace of the central involution is nonzero and invariant.
Choose a section `Sp_4(Z)->E_2`.  Restriction to this spectral subspace turns
the section into an exact finite-dimensional projective representation; its
multiplier is precisely the order-two metaplectic, or Maslov half, class.
