---
rg: 2
id: rotated-frame-universe-rich-2to1-game-has-vanishing-value
kind: claim
title: The rotated-frame universe rich 2-to-1 game U_n has val(U_n) -> 0 over all Borel strategies
distinct_from:
  walsh-frame-rich-2to1-games-have-value-near-one: that proves value near 1 for Walsh-framed perfect SDP solutions via forcing edge mass; U_n has no forcing edges (its pair-difference rotations are Haar on O(n)), so the forcing invariant is zero here and the question is genuinely about noise stability.
  rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps: that transfers whatever val(U_n) is to finite instances; this is the value question itself.
artifacts:
  - experiments/rich-2to1-rotated-frame-universe-2026-09-17/rotated_frame_strategies.py
  - experiments/rich-2to1-rotated-frame-universe-2026-09-17/linear_strategy_reduction.py
  - experiments/rich-2to1-rotated-frame-universe-2026-09-17/check_universe_identities.py
---

**OPEN.** `U_n` is defined in
`rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps`. The claim is
that for every `delta > 0` there is `n` with `val(U_n) <= delta`. By that node,
this is the one missing input for robust basic-SDP gaps for BKM Conjecture 7 at
a fixed alphabet. A Borel strategy with `val(U_n) >= c > 0` for all `n` would
refute this claim. It would not give an algorithm, but it would remove the
canonical symmetric candidate gap.

**Established facts used below.**

1. *Walk form and conservation.* Given `(Y, P)`, the neighbour is
   `X' = K X` with `K` Haar on `K_P = H_P (I_n x O(n)) H_P^T`. Every `K_P`
   fixes the all-ones vector of the label space, so `w = sum_a x_a` is
   conserved.
2. *Second-moment reduction.* Let `S_e = {f in e}` for a pair `e = {a,a'}`,
   and let `T_P` be the conditional expectation onto the pair sums of `P`, a
   projection. Put `T_e = E_(P containing e) T_P`. By
   `max_b mu_b <= (sum_b mu_b^2)^(1/2)`, Jensen in `P`, and
   `Pr[e in P] = 1/(2n-1)`:
   `val(U_n)^2 <= (1/(2n-1)) sum_e <1_(S_e), T_e 1_(S_e)>`.
3. *Why a spectral gap is not enough.* Every `K_P` with `P` containing `e`
   fixes `e_a + e_a'` and the all-ones vector, so every Borel function of
   `(w, x_a + x_a')` is `T_e`-invariant. On degree-1 functions orthogonal to
   these, `T_e` has eigenvalue about 1/2 (heuristic, not proved). A
   spectral-gap bound
   `<1_S, T_e 1_S> <= ||E[1_S | invariant algebra]||^2 + lambda mu(S)` gives no
   decay by itself: the `lambda mu(S)` terms sum to a constant, and the
   invariant term is uncontrolled.

**Decomposition (each part can fail on its own).**

- (A1) *Small-set expansion modulo the invariant algebra.* For
  `mu(S) <= 1/n`,
  `<1_S, T_e 1_S> <= ||E[1_S | w, x_a+x_a']||^2 + o_n(1) mu(S)`.
  This is a hypercontractive statement for averages of conjugate `O(n)` Haar
  projections inside `O(2n)`. It fails if `T_e` has a sparse near-1
  eigenfunction outside the pair-sum algebra.
- (A2) *No consistent pair-sum-measurable partition.* No Borel `f` makes
  `S_a union S_a'` close to `(w, x_a + x_a')`-measurable on a set of pairs
  carrying constant total weight. This is an exact rigidity question on
  orthonormal frames. It fails if some selection rule is "pair-sum local",
  which would be the continuous analogue of the forcing mass in the Walsh
  node.

(A1) and (A2) give `val(U_n)^2 <= o(1) + (1/(2n-1)) sum_e ||E[1_(S_e) | w, x_a+x_a']||^2`,
and (A2) makes the last term `o(1)`.

## Attempts

- 2026-09-17, e-ugc-pull-transplant (transplanter via finite-models):
  numerical test of argmax-of-potential strategies `f(X) = argmax_a h(x_a)`.
  - Held-out estimates, 200 right vertices, 400 edges each
    (`rotated_frame_strategies.py`). Values at `n = 4, 8, 16, 32`:
    - linear `<x,u>`: 0.69, 0.55, 0.48, 0.40;
    - `|<x,u>|`: 0.60, 0.46, 0.41, 0.34;
    - l4 over 4 directions: 0.48, 0.41, 0.31, 0.26;
    - l-infinity coordinates: 0.37, 0.23, 0.17, 0.12;
    - random quadratic: 0.56, 0.41, 0.29, 0.22.
  - The linear strategy reduces exactly to `alpha_b + |beta_b|` with `beta`
    a fresh uniform sphere vector (`linear_strategy_reduction.py`). Values at
    `n = 64, 256, 1024, 4096`: 0.34, 0.24, 0.18, 0.13. The local exponent is
    about `-0.22`.
  - Heuristic upper bound for linear: the champion `alpha` is about
    `sqrt(2 log n)` and the maximum of `alpha + |beta|` is about
    `2 sqrt(log n)`, so the probability is at most
    `n^(-(2-sqrt2)^2/2 + o(1)) = n^(-0.17+o(1))`. This is a sketch, not written
    as a proof.
  - Belief unchanged: every tested class decays polynomially, slowly. The best
    one (linear) needs `n` around `delta^(-4.5)` to reach `delta`. No general
    argument covers non-potential strategies. Open steps: (A1) and (A2) above.
