---
rg: 2
id: cyclic-carrier-energy-stability
kind: claim
title: Preserve one strict finite-dimensional cyclic-energy ceiling under matrix ultraproduct limits
artifacts:
  - research/artifacts/cyclic-carrier-energy-and-outlier-audit-2026-08-21.md
distinct_from:
  matrix-only-cyclic-carrier-invariance: that forces approximate cyclic energy to zero; this permits nonzero exact finite-dimensional energy and asks only that one scalar supremum not jump above its exact ceiling.
  leavitt-steinberg-hs-stable: that asks to perturb whole approximate representations to exact ones; this asks upper semicontinuity of one fixed trace-polynomial energy and no operator correction.
  non-ce-bcs-has-robust-approximate-energy-gap: that is a lower gap for additive BCS relations; this is an upper ceiling for a cyclic commutator energy in approximate group representations.
---

Construct finitely presented data `G=<X|R>`, `H=<S><=G`, an infinite-order
word `w`, and a nonconstant trigonometric polynomial `f`. Define

```text
E(U)=sum_(s in S)||[U(s),f(U(w))]||_2^2,
beta_fd=sup_(pi exact finite-dimensional) E(pi),
beta_app(delta)=sup_(d,U:def_R(U)<=delta) E(U),
E_reg=E(lambda_G).
```

Require

```text
beta_fd<E_reg,
limsup_(delta->0) beta_app(delta)<=beta_fd.              (CES)
```

Equivalently, every matrix-ultraproduct homomorphism has this one scalar
energy at most the exact finite-dimensional ceiling. No closeness to an
exact representation is required.

## Attempts

- `shifted-infinite-heisenberg-wreath-exact-mci-is-hyperlinear` realizes the
  strict exact gap with `beta_fd=0`, but its hyperlinear models violate
  `(CES)`. Exact finite-dimensional classification alone is therefore
  insufficient.
- Residually finite candidates are impossible: a finite quotient injective
  on the finite supports defining `E` has quotient-regular energy exactly
  `E_reg`.
- Full HS stability would prove `(CES)` but is far stronger than needed and
  is unavailable for infinite hyperlinear property-`(T)` groups. The live
  target is one-polynomial upper semicontinuity, potentially from a
  finite-dimensional multiplicity or holonomy invariant.
