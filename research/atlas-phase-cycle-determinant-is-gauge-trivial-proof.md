---
rg: 2
id: atlas-phase-cycle-determinant-is-gauge-trivial-proof
kind: route
title: Cancel determinants and scalar gauge on every transported Atlas phase edge
target: atlas-phase-cycle-determinant-is-gauge-trivial
requires: []
---

For every chart word `x`,

```text
Phi_x(U)=rho(x) U rho(x)^*.
```

Hence

```text
det(Phi_x(U))=det(U).
```

For an oriented phase edge

```text
E_(u,v)(U)=Phi_u(U) Phi_v(U)^*,
```

we therefore have identically

```text
det E_(u,v)(U)
 = det(U) overline(det(U))
 = 1.
```

Every boundary or interior multiplicative holonomy is a product of such
edges, so its determinant is also one before any Atlas relation is imposed.

Now let `zeta` be scalar.  Conjugation by `rho(x)` fixes scalars, so

```text
Phi_x(zeta U)=zeta Phi_x(U).
```

The scalar cancels from every edge:

```text
E_(u,v)(zeta U)=E_(u,v)(U).
```

On the other hand every additive circulation is linear in the transported
chart unitary, hence

```text
L_j(zeta U)=zeta L_j(U).
```

Thus all singular values and every unitarily invariant norm of every
`L_j` are unchanged.  Given any prescribed determinant `eta`, choose a
`d`th root `zeta` with

```text
zeta^d=eta det(U)^(-1).
```

Then `det(zeta U)=eta` while all phase energies occurring in the Atlas lift
are exactly unchanged.  The determinant of the relative chart gauge is
therefore free on every phase-energy fibre.

Finally, every `L_j(U)` and every individual phase difference is a square
finite-dimensional operator, so its Fredholm index is zero.  Rectangular
stacking can record only the fixed source-minus-target dimension, independent
of the Atlas arrow.  Hence determinant phase, phase-cycle determinants and
Fredholm index cannot supply the missing finite-matrix phase lift.