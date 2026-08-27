---
rg: 2
id: atlas-phase-cycle-determinant-is-gauge-trivial
kind: claim
title: Every Atlas phase-cycle determinant is scalar-gauge trivial
distinct_from:
  fixed-rank-index-authenticator-has-gap-or-functoriality: that gives the general HS continuity dichotomy for fixed matrix-polynomial invariants; this proves an exact symmetry of the twenty-seven Atlas phase reduction before continuity is considered.
  atlas-independent-phase-incidence-is-not-coercive: that frees the phase occurrences and constructs cancelling private edges; this retains the common conjugation orbit and shows determinant data are nevertheless identically blind.
  atlas-five-row-operator-phase-lift: that asks for a norm inequality between additive circulations and multiplicative holonomies; this eliminates determinant and Fredholm index as possible finite-only invariants for proving that inequality.
---

**ESTABLISHED FIREWALL.**  In the exact twenty-seven-phase reduction, put

```text
Phi_x(U)=rho(x) U rho(x)^*                             (PCD1)
```

on a `d`-dimensional regular Atlas multiplicity.  For every phase edge

```text
E_(u,v)(U)=Phi_u(U) Phi_v(U)^*,                        (PCD2)
```

one has identically, before imposing any Atlas relation,

```text
det E_(u,v)(U)=1.                                     (PCD3)
```

Hence the five boundary holonomies and the interior holonomy all have
determinant one for **every** relative chart unitary.  Their determinant
equations contain no information about the six nonlinear defects.

There is a stronger scalar-gauge statement.  For every `zeta in T`,

```text
Phi_x(zeta U)=zeta Phi_x(U),
E_(u,v)(zeta U)=E_(u,v)(U).                            (PCD4)
```

Thus all six multiplicative holonomies are fixed by `U -> zeta U`, while
every additive phase circulation

```text
L_j(U)=sum_r(Phi_(u_jr)(U)-Phi_(v_jr)(U))             (PCD5)
```

is merely multiplied by `zeta`.  Its complete singular-value list and every
unitarily invariant norm are unchanged.  Given any desired
`eta in T`, choose a `d`th root satisfying

```text
zeta^d=eta det(U)^(-1).
```

Then `det(zeta U)=eta` with every quantity occurring in the five-row
inequality unchanged.  The determinant phase of the relative chart gauge is
therefore completely free on each phase-energy fiber.

Finally, each `L_j(U)` and each individual phase difference is square, so
its finite-dimensional Fredholm index is zero.  Stacking such maps into a
rectangular operator produces only the source-minus-target dimension index
of `fixed-rank-index-authenticator-has-gap-or-functoriality`, independent of
the Atlas arrow.

Consequently determinant phase, determinants of the six holonomies, and
Fredholm index cannot supply the finite-matrix-only extraction left in
`atlas-kernel-relators-couple-cross-gram-to-four-pauli` or prove
`atlas-five-row-operator-phase-lift`.  A surviving mixed invariant must use
the *relative singular subspaces* of several operators (for example a
shrunk-space certificate), not determinant or index data.
