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
`block-adaptive-sparse-reset-is-cheap`.  Its weighted counting input is now
explicit: `central-weighted-erasure-ledger-recovers-reset-density` cleans
every block in range, resets exceptional blocks in full, and bounds the
trace-weighted coordinate density by `C E_par/rho^2`.  Thus the central
branch loses no factor of `L`; only construction of the reducing
decomposition remains.  On the complement, combine the
little-o two-odd-factor estimate with
`one-anchor-grading-makes-parity-damage-quadratic`.

There is no exponent conflict between hard reset and the soft anchor step.
`hard-soft-exponent-conflict-is-a-norm-mismatch` observes that the
quadratic remainder is an `L_2` row amplitude `Ct sqrt(E)` and therefore
only changes the linear contraction coefficient by `Ct`.  A fixed small
`t`, or `t=E^alpha` with `0<alpha<1/2`, is compatible with vanishing reset
cost `E/t^2`.  The sole threshold issue is constructing the operator-small
reducing pieces and summing their boundaries.

One local noncentral step is now complete.
`one-anchor-odd-spike-has-a-cheap-reducing-cut` thresholds
`R_(a,i)=Y_(a,i)^2`.  Its average boundary against all generators is
controlled by `q_i+q_a`; coarea produces a reducing correction of cost
`O((q_i+q_a)/t)`, the high block is cheaply reset, and the complement has
`R_(a,i)<=2t`.  The remaining theorem is a selection/summability statement
for these cuts, not a missing one-spike estimate.

Parity supplies the correct one-cut charge.
`localized-loewner-pays-spike-or-boundary` tests max-fractional Loewner
order on `Q_ap`: either a high odd-square cut has boundary at least
`kappa s tau(p)`, or the full anchor row on that block pays at least
`(kappa/4)s tau(p)`.  The row-paid alternative sums over disjoint reducing
cuts without losing `L`.  In addition, `(OSC7)` bounds a coarea-selected
boundary linearly by the high spectral first moment.  The remaining task is
to order boundary-heavy cuts so that this high-tail mass is not reused.

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
Naively invoking the local cut for every `(a,i)` is not enough: its boundary
cost is linear in `q_i+q_a`, and the same commutator row can be charged
`Theta(L)` times.  A stopping rule must select disjoint physical mass or
prove geometric decay before the next cut.
