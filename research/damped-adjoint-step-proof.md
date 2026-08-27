---
rg: 2
id: damped-adjoint-step-proof
kind: route
title: Apply one Landweber step to the normalized complete-overlay Jacobian
target: damped-adjoint-step-bypasses-code-riesz-at-exact-base
requires:
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
---

On the orthogonal complement of the simultaneous-conjugation kernel,
`quadratic-overlay-has-uniform-linearized-synchronization-gap` places the
spectrum of `D*D` in `[kappa,M^2]`.  Functional calculus applied to
`I-eta D*D`, for `eta<=M^(-2)`, gives `(DAS3)`.

For the amplification estimate, write every complete-pair derivative as
the sum of its two coordinate terms.  The adjoint collects either term by
a normalized average in the unused coordinate.  Kadison--Jensen for that
average, followed by summing the retained coordinate, proves `(DAS4)`;
apply the same calculation to adjoints for the row norm.  Bounded-template
layers have a fixed incidence bound and are handled by finite
Cauchy--Schwarz.  Consequently `D*` is uniformly row-column bounded even
though the Moore--Penrose inverse of `D` is the unresolved code-Riesz
multiplier.  One damped adjoint step contracts in `L_2`, and iteration gives
any fixed linear accuracy with constants independent of length and matrix
dimension.
