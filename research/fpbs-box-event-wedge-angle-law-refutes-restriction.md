---
rg: 2
id: fpbs-box-event-wedge-angle-law-refutes-restriction
kind: claim
title: For the FPBS pinch-wall box event D'_n(X_theta) with target wedge |arg z| < theta, the exponent zeta(theta) is at least the one-arm exponent 5/48 for every theta, and FKG splits the gate zeta(pi/2) < 3/8 into the one-quadrant bound rho < 3/16, which the data put out of reach (rho ~ 0.211); the proposed SLE_6-exploration/restriction-wedge route (exponent alpha(pi+theta)/(pi-theta)) is refuted, since it forces zeta(pi/2) = 3 zeta(0), while triangular-lattice data give zeta(0) ~ 0.149 and zeta(pi/2) ~ 0.256
distinct_from:
  fpbs-cle6-hull-wedge-event-is-not-the-box-event: that separates the CLE_6 hull event from the box event at the single angle pi/2 and names D'_n as the target; this proves a floor valid at every angle and a rigorous FKG reduction of the gate to a one-quadrant event (shown numerically lossy), and refutes the restriction-wedge mechanism for D'_n itself through its angle dependence
artifacts:
  - research/fpbs-box-event-wedge-angle-law-refutes-restriction-proof.md
  - experiments/fpbs-pinch-wedge-angle-2026-09-18/tri_wedge.c
  - experiments/fpbs-pinch-wedge-angle-2026-09-18/pool.py
  - experiments/fpbs-pinch-wedge-angle-2026-09-18/run_all.sh
  - experiments/fpbs-pinch-wedge-angle-2026-09-18/results.txt
---

**Status.** Lemmas 1-3 and Corollary 3.1 are ESTABLISHED: monotonicity in
the target, the one-arm floor, and the FKG half-split (proofs in
`fpbs-box-event-wedge-angle-law-refutes-restriction-proof`). The
refutation of the restriction-wedge mechanism (M1), and the failure of
the half-split to close the gate, combine Proposition 4.1
(ESTABLISHED, given the M1 ansatz) with NUMERICAL exponents. (H) stays
OPEN. The quadrant bound `rho < 3/16` is numerically false.

**Setting.** Triangular site percolation at `p = 1/2`, wired hexagon
`B_n`, boundary cluster `I_n`, negative axis `S_n`, as in
`fpbs-cle6-hull-wedge-event-is-not-the-box-event`. For a set `Y`,
`D'_n(Y)` says that no non-`I_n`, pinch-free path joins `Y` to `S_n`, and
`D_n(Y)` says that no white circuit around a site of `S_n` meets `Y`. Take
`X_theta = {|arg z| < theta}`, so `X_{pi/2} = {x > 0}` is the case (H)
needs, and let `X^+ = {x > 0, y >= 0}`. Write
`P(D'_n(X_theta)) = n^{-zeta(theta)+o(1)}` and
`P(D'_n(X^+)) = n^{-rho+o(1)}`.

**Theorem.**

(a) *Floor.* `D'_n(theta) ⊆ D_n(theta) ⊆ {a black arm from N_2[0] to
∂B_n}`. Hence `zeta(theta) >= 5/48` for every `theta`, and
`rho >= 5/48`. The reason is that the outer boundary of the filled
black clusters at the origin is a white circuit, and it always crosses
the positive axis.

(b) *Half-split.* `D'_n = D'_n(X^+) ∩ D'_n(X^-)`, where both events are
increasing and are exchanged by a lattice reflection. So
`P(D'_n) >= P(D'_n(X^+))^2`. Consequently `P(D'_n(X^+)) >= c n^{-rho'}`
with `rho' < 3/16` implies (H), and the admissible window is
`rho ∈ [5/48, 3/16)`. Numerically `rho = 0.211(7)`, outside the window.
The two halves are strongly positively correlated
(`2 rho ≈ 0.42` against `zeta(pi/2) ≈ 0.256`), so this decorrelation
loses about `0.17` and cannot close the gate by itself.

(c) *The restriction-wedge route fails.* Open the slit by `sqrt`. Any
bound that realises `D'_n(theta)` as a restriction-sample avoidance
event of one exponent `alpha` gives
`zeta(theta) = alpha(pi+theta)/(pi-theta)`, so `zeta(pi/2) = 3 zeta(0)`.
Applied at `theta = 0` it needs `alpha >= zeta(0)`, and then at
`theta = pi/2` it certifies only `n^{-3 alpha}`. Rigorously, by (a),
`3 alpha >= 5/16`. Numerically `3 alpha >= 0.447(12) > 3/8`. The standard
laws are further off: SLE_{8/3} gives `15/8`, and the SLE_6 hull gives
`1`.

**Numerics** (`tri_wedge.c`, 6000 nested samples each, `n = 16..256`,
pooled slopes with jackknife errors):

| event | zeta | `P(D'_256)` |
|---|---|---|
| `D'_n(0)`, positive axis | 0.149(4) | 0.399 |
| `D'_n(pi/2)`, `x > 0` | 0.256(6) | 0.197 |
| `D'_n(X^+)`, quadrant | 0.211(7) | 0.268 |

The ratio is `zeta(0)/zeta(pi/2) = 0.58(2)`. The restriction law predicts
`1/3`, and plain conformal covariance in the unslit plane
(`zeta ∝ 1/(pi - theta)`) predicts `1/2`. Neither fits: the event is not
a single-exponent conformally covariant wedge event at these sizes. The
one-arm check reproduces `5/48`, and there are no monotonicity
violations.

**What this leaves.** Two cheap routes from `D'_n` to (H) are closed:

* restriction/SLE bounds in the slit picture, which are off by the angle
  law;
* decorrelation of the two halves, which is off by the correlation.

These are failures of the proof mechanisms, not of (H). The measured
`zeta(pi/2) = 0.256(6)` sits well below `3/8`. Any proof must bound the
full two-sided event directly. It must also allow the angle dependence
`zeta(pi/2) < 2 zeta(0)`, which neither a restriction factorization nor
the FKG product can produce.

**Next.** Prove `P(D'_n(pi/2)) >= c P(D'_n(0))^{2}` (numerically
`0.256 < 0.298`), and bound `zeta(0) < 3/16` for the axis-to-axis event.
Together these give (H). The first says that widening the target from the
positive axis to the half-plane costs less than a second independent copy
of the axis event. The axis event `D'_n(0)` has no bulk target: the wired
cluster must separate the two half-axes through pinches. This makes it a
two-boundary-arc event, which is the natural object for an exact
external-perimeter (SLE_{8/3}-type) computation in the unslit plane.
