---
rg: 2
id: central-adaptive-peeling-or-noncentral-stopping
kind: claim
title: Centrally adapt sparse peeling or produce a noncentral stopping projection
distinct_from:
  sparse-peeling-before-anchor-fourth-moment-dichotomy: that incorrectly requires one global coordinate set; translated sparse blocks refute it.
  block-adaptive-sparse-reset-is-cheap: that proves terminal repair after central reducing sets are available; this must manufacture those sets or handle genuinely noncentral overlap.
  balanced-overlay-common-reducing-outlier-cut: that gives one physical cut from the raw residual square function; this needs a joint coordinate-and-physical stopping decomposition adapted to anchor-odd products.
---

OPEN.  Starting from the all-dual Loewner inequalities and the positive
operators `Y_(a,i)^2`, construct either:

1. a central reducing decomposition `(z_omega)` with coordinate sets
   `U_omega` of trace-weighted density `o_E(1)`, capturing all sparse
   fourth-moment mass up to `o(1)` of anchor energy; or
2. a genuinely noncentral physical projection charged by the balanced raw
   square function, after whose removal the same little-o bound holds.

The central branch is terminal by
`block-adaptive-sparse-reset-is-cheap`.  On the complement, combine the
little-o two-odd-factor estimate with
`one-anchor-grading-makes-parity-damage-quadratic`.

## Attempts

For every vector state, the Loewner shortened-core inequalities give a
scalar layer-cake peeling and hence a vector-dependent coordinate set.  If
these sets are constant on central reducing blocks, the first branch above
applies.  The obstruction is pasting arbitrary vector-state choices:
spectral projections of different `Y_(a,i)^2` need not commute with one
another or with the generators, so choosing coordinates separately on each
vector is nonlinear and does not define corrected reflections.

The translated three-site mixture proves that demanding one global set is
impossible, but it is solved exactly by central adaptation.  Therefore a
counterexample to the corrected dichotomy must have genuinely noncentral,
overlapping spike projections.  The next quantitative target is a
noncommutative layer-cake statement which either approximately centralizes
those projections (feeding branch 1) or charges their commutator/boundary
to the common covariant residual square function (feeding branch 2).
