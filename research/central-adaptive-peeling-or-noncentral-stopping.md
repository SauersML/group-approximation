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

The terminal composition is now packaged in
`central-reducing-spike-certificates-batch-round`.  Once the reducing
decomposition has cleaning sets which cover every high odd spike, reset all
sets simultaneously.  The cost is `C E/rho^2`, independent of how many
historical cuts produced the blocks, and the complement retains the stated
operator cutoff.  Thus the central branch's only missing assertion is the
coverage certificate itself; counting, repeated-cut multiplicity, and
balanced-energy bookkeeping are closed.

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

The local decision is now quantitative as well.
`single-spike-split-or-charge-has-fourth-root-modulus` chooses the
`R=Y^2` threshold at `t=(q_i+q_a)^(1/2)`.  If the actual projection boundary
is at most `(q_i+q_a)^(1/4)` times its trace, block diagonalization costs
that small relative amount; otherwise the whole spike projection has trace
`O((q_i+q_a)^(1/4))`.  The retained odd operator norm has the same
fourth-root modulus.  Thus only repeated-cut overlap remains: select these
local split-or-charge decisions without charging one pair row many times.

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

`standard-nc-stopping-theorems-miss-overlap-ledger` audits the three standard
imports at precisely this point.  Cuculescu/Gundy stopping requires one
martingale in one filtration and yields no product-form physical cut after
diagonal amplification; normalized-HS almost-commuting rounding assumes all
pairwise commutators for a fixed-size tuple; and Frieze--Kannan weak
regularity produces scalar rectangles in cut norm, not reducing physical
projections.  Thus none supplies the missing no-reuse ledger from the current
hypotheses.  A viable theorem must instead preserve the localized parity
charge while producing nested/disjoint cuts or geometric decay of one common
high-tail potential.

One need not pay global block-diagonalization at every cut.
`spectral-cut-anchor-reset-pays-boundary-in-one-row` uses the fact that a
spectral cut of `Y_(a,i)^2` already commutes with the anchor.  Resetting only
that anchor on the cut costs `O(tau(p)/L)` and sends the nonreducing
boundary into only its complete-pair row, hence at cost `D(p)/L`.  Combined
with localized Loewner, row-paid cut mass is summable at the correct
normalization.  The exact last case is boundary reuse: after a nonreducing
reset, new odd mass may be generated by the same `D(p)/L`; prove that the
high-tail coarea ledger decreases geometrically, or exhibit a cycle which
reuses it.

The anchor sign supplies a monotone cross-iteration potential.
`odd-spectral-anchor-resets-have-monotone-sign-budget` proves that every
positive odd-square cut has exactly half its trace in the current negative
anchor sector.  Resetting deletes that half, so for each anchor
`sum_n tau(p_(a,n))<=2tau(e_(a,-))`, even for overlapping physical cuts.
Boundary leakage cannot recreate negative mass.  Together with the
fourth-root small-mass alternative, the reset COST is summable.  But
`monotone-anchor-sign-budget-does-not-give-stagewise-coverage` shows that
one cut per anchor per stage need not give coverage: `N` disjoint central
zero-boundary spikes require `N` cuts while saturating the same sign budget.
The residual scheduling theorem must therefore batch a weighted family of
central cuts or use balanced parity to rule out that profile; monotonicity
alone is insufficient.

The literal one-shot join is too discontinuous.  Noncommutativity of the
cuts is not the essential obstruction.
`orthogonal-odd-cut-join-amplifies-boundary-linearly` gives orthogonal
high cuts with anchor-tail and complete-pair energy `O(1/L)` but join
boundary `1-O(1/L)`.  Each site reflection preserves its own cut while
moving every other cut outward.  Hence no generic coarea/complete-overlay
estimate can charge the join without a linear loss.  Any surviving join
route must use the all-dual parity/Loewner faces to forbid this labelled
cross-boundary profile (or retain the labels instead of taking the bare
join).

There is a condition-number-free replacement.
`regularized-anchor-square-function-has-dimension-free-cut` thresholds the
average `K_a=L^(-1)sum_iY_(a,i)^2`, rather than the join of its summand
supports.  On the retained block its operator norm is at most `2theta`;
averaged over anchors, deleted trace is `O(E_pair/theta)` and cut boundary
is `O(sqrt(E_pair)/theta)`.  Moreover
`regularized-anchor-cut-makes-residual-spikes-boundary-heavy` uses the
all-dual Loewner inequality to show that, for `theta<=kappa s/16`, every
remaining compressed `s`-spike has boundary at least
`(kappa s/3)` times its trace.  Thus coverage no longer needs a bare join.
The remaining stopping issue is to transport the aggregate cut's `L_2`
leakage through the nonlinear contraction, or to exactify the cut without
creating a new retained operator-norm spike.

The commutator boundary itself also has an exact monotone ledger.
`anchor-reset-row-sign-trace-is-sharp-lyapunov` proves that the anchor's
averaged commutator-row energy plus `8tau((1-A)/2)` is nonincreasing under
every commuting-block reset; the coefficient is sharp already in `M_2`.
Thus a boundary term cannot cycle indefinitely without consuming monotone
negative-sign mass.  This still does not close the claim: the initial sign
reservoir is order one, whereas basin capture needs little-o cost, and the
disjoint central-spike profile above can spend it arbitrarily slowly.  The
remaining stopping rule must batch weighted cuts or prove coverage while
consuming only vanishing trace-weighted sign mass.
