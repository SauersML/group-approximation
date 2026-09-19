---
rg: 2
id: atlas-phase-cycle-determinant-gauge-proof
kind: route
title: Cancel determinants edgewise and rotate the common relative gauge
target: atlas-phase-cycle-determinant-is-gauge-trivial
requires:
  - fixed-rank-index-authenticator-has-gap-or-functoriality
---

Conjugation does not change determinant, so `(PCD1)` gives

```text
det Phi_x(U)=det U.
```

Taking the determinant of `(PCD2)` therefore yields

```text
det E_(u,v)(U)=det(U) overline(det(U))=1.
```

Every nonlinear row in `(FPL5)--(FPL6)` is a product of these edges, proving
`(PCD3)` for the five boundary cycles and the interior cycle.

Scalar multiplication commutes with `rho(x)`, proving the first identity in
`(PCD4)`; the scalar and its adjoint then cancel in every edge, proving the
second.  Formula `(PCD5)` is linear in the transported copies of `U`, so

```text
L_j(zeta U)=zeta L_j(U).
```

Multiplication by a scalar unitary leaves singular values and unitarily
invariant norms unchanged.  The map `zeta -> zeta^d` is onto the circle, so
the displayed choice of `zeta` sets `det(zeta U)` arbitrarily without moving
any phase energy.

For the index statement, a square finite-dimensional linear map has

```text
dim ker A-dim ker A^*=0
```

by rank-nullity.  For a rectangular stacking, equation `(FRI2)` identifies
the index with the fixed source-target dimension difference.  Neither case
reads the relative chart position.  This completes the firewall.
