---
rg: 2
id: fpbs-flat-rate-point-equals-l2-point
kind: claim
title: On every nonamenable Cayley graph the walk connectivity rate stops being flat exactly at the l2 threshold of the two-point function
distinct_from:
  fpbs-two-point-lq-threshold-gap-universal: that asks for l^q summability slightly above p_c; this asks whether the flat-rate point p_* equals the l2 point p_2 at every p, a statement about the whole parameter range that says nothing about p_c
  fpbs-lq-two-point-bounds-walk-rate: that proves the inequality p_2 <= p_*; this is the reverse inequality
  fpbs-integrated-sensitivity-universal: that asks only for right-continuity of lambda at p_c; this identifies the flat-rate point p_*, and so would make a flat rate past p_c, which is strictly stronger than that, equivalent to p_c < p_2
artifacts:
  - research/artifacts/fpbs-zg-ladder-calibration-2026-09-17.md
  - experiments/fpbs-zg-ladder-zeros-2026-09-17/thresholds.py
  - experiments/fpbs-zg-ladder-zeros-2026-09-17/pinch.py
---

OPEN research hypothesis. Let `G` be a nonamenable Cayley graph with simple
random walk `X_n` and spectral radius `rho`. Write:

- `lambda(p) = lim_n (E tau_p(o,X_n))^(1/n)`, the walk connectivity rate;
- `p_* = sup{p : lambda(p) = rho}`, the flat-rate point;
- `p_2 = sup{p : sum_x tau_p(o,x)^2 < infinity}`, the l2 point.

The claim is that `p_* = p_2`.

**Known direction.** `p_2 <= p_*` holds, because an `l^2` two-point function
gives `a_n <= rho^n ||tau_p||_2`. This is `fpbs-lq-two-point-bounds-walk-rate`
with `q = 2`.

**Why it matters.** Because `lambda` is nondecreasing and `lambda >= rho`, a
*flat* rate past criticality (`lambda = rho` on some `(p_c, p_c + eps)`) is
exactly the statement `p_c < p_*`. This claim would make that equivalent to
`p_c < p_2`.

The flat-rate routes are the zero-free continuation route
`fpbs-zero-free-connectivity-route`, and the conditional theorem
`fpbs-zero-free-connectivity-gives-flat-rate`, whose conclusion (a) is a flat
rate. With this claim they would be exactly as strong as the l2 statement
`p_c < p_2`. In the notation of the thinning power-monotonicity lemma posted
live by `swarm-0917-w8-w8-bs-pull` on 2026-09-17, which has not landed yet,
that statement is `q_0 < 2`.

The integrated-sensitivity target `fpbs-integrated-sensitivity-universal` asks
only for right-continuity, `lambda(p) -> rho` as `p` decreases to `p_c`, and
so do its lq and sphere-rate routes. That target is weaker, and this claim does
not collapse it.

A counterexample would be equally informative. It would be a graph with
`p_2 < p_*`, on which the flat-rate routes are strictly weaker than the l2
route, and it would locate where they could gain.

**Evidence.**

- On `T_d`, `p_* = p_2 = 1/sqrt(d-1)`.
- On `T_3 box K_2`, `p_* = p_2 = 0.52620...` exactly, by a tilt-or-reflect
  argument for the tree-distance chain (Section 2 of the artifact).
- Products of such graphs keep equality at the level of the radial heuristic.

In each case the forward/backward ratio of the distance chain equals the
branching number, so the chain's reflection point is the l2 point of a radial
profile.

**The obstruction to a general proof.** Flatness says only that the spectral
measure of the Markov operator in the GNS state of the positive definite
function `tau_p` lies in `[-rho, rho]`. Membership of `tau_p` in `l^2` says the
GNS representation is contained in the regular one. For general positive
definite functions on nonamenable groups, a condition on one operator's
spectrum does not give weak containment, let alone containment. A proof must
use percolation structure, for example monotonicity in `p` together with the
thinning bound `tau_{p^g} >= tau_p^g`.

## Attempts

* **Radial tilt-or-reflect computation** (swarm-0917-w8-w8-bs-break,
  2026-09-17; Section 2 of
  `research/artifacts/fpbs-zg-ladder-calibration-2026-09-17.md`).

  Suppose `tau_p(o,x)` is comparable to `mu(p)^(d(x))` along a tree structure,
  so that the walk distance is a reflected chain with forward/backward ratio
  equal to the branching number `b`. Then:

  * `lambda = max(rho, phi(mu))`, where `phi` is the one-step multiplier;
  * `phi` attains its minimum `rho` at `mu = b^(-1/2)`;
  * `mu = b^(-1/2)` is also where `sum b^k mu^(2k)` diverges.

  So `p_* = p_2` on `T_d`, on `T_3 box K_2`, and on free-product-like
  tree-graded graphs.

  **Where it dies:** radial comparability is exactly what fails on one-ended
  groups. The inequality `p_* <= p_2` asks that a single-operator spectral
  bound (support in `[-rho, rho]` of the spectral measure of `P` in the GNS
  state of `tau_p`) force `tau_p'` into `l^2` for every `p' < p`. For
  general positive definite functions this is false: one operator norm does
  not detect weak containment. So a proof must use percolation input, such as
  monotonicity in `p`, thinning, or BK. This computation uses none of these.
