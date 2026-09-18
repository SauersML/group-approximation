---
rg: 2
id: qudit-weyl-rounding-sharp-constant
kind: claim
title: The sharp additive stabilizer rounding constant for prime-qudit Weyl sums is d/pi + O(1)
artifacts:
  - experiments/qudit-stabilizer-rounding-constant-2026-09-17/README.md
refuted_by:
  - qudit-weyl-rounding-constant-triangular-harper-bound
distinct_from:
  qudit-weyl-rounding-constant-linear-upper-bound: that proves the upper bound 2/sin(pi/d)+3, about 2d/pi; this asks for the sharp constant, conjectured to be about d/pi, with rigorous lower bounds and numerics.
  stabilizer-rounding-constant-is-one-over-sqrt2: that is the sharp qubit constant 1/sqrt2; this is the prime-qudit analogue, which grows linearly in d.
---

**OPEN (conjecture with rigorous lower bounds and numerics).** Let `c_d` be the least
constant such that every explicit Weyl decomposition `K = sum_j c_j g_j` on any number of
prime-`d` qudits, with weight `W`, has a stabilizer state with
`<phi|K|phi> >= lambda_max(K) - c_d (W - lambda_max(K))`.

*Conjecture.* `c_d = d/pi + O(1)`. Numerically `c_d` is about `d/pi - 0.2` for small `d`.

**Proved bounds.**
- Upper: `c_d <= 2/sin(pi/d) + 3` (`qudit-weyl-rounding-constant-linear-upper-bound`).
  `c_2 = 1/sqrt2` (`stabilizer-rounding-constant-is-one-over-sqrt2`).
- Lower, antiparity (all `d+1` MUB directions at once):
  `K = -sum_(v != 0) D(v) = I - d A_0`, where `A_0` is the parity (phase-point)
  operator, with eigenvalues `+-1`. Then `lambda_max = d + 1` and `W = d^2 - 1`. A
  stabilizer state has `<A_0> = d W_phi(0) in {0, 1}`, so the best stabilizer value is
  `1`. The ratio is `d/((d-2)(d+1))`, which is `3/4` at `d = 3` and decays afterwards.
- Lower, Harper (one direction pair): `K = Z + Z^* + X + X^*`, `W = 4`. On one qudit a
  stabilizer state is a `Z`-, `X`- or mixed-basis state, so the best stabilizer value is
  `2`. Numerically `lambda_max(K) = 4 - 2pi/d + O(d^(-2))`, as expected from the
  harmonic-oscillator ground state of the Harper operator; this is not proved here.
  Then the ratio is `(lambda - 2)/(4 - lambda) = d/pi - O(1)`. Computed values: `0.935, 1.510, 2.765, 3.399, 9.12, 18.67, 31.40, 66.41` for
  `d = 5, 7, 11, 13, 31, 61, 101, 211`.
- So the upper bound is linear in `d` (proved), and the lower bound is `d/pi - O(1)`. The
  lower bound is checked by computation for each listed `d`; the asymptotic is numerical.
  The expected leading coefficient lies in `[1/pi, 2/pi]`.

The expected extremal "sum over the `d+1` MUB directions" is extremal only at `d = 3`.
For `d >= 5` the one-qudit optimum is not antiparity, and Harper-type sums beat it.

**Numerics** (`experiments/qudit-stabilizer-rounding-constant-2026-09-17/`). The
state-side dual LP is `c(psi) = min c` such that a stabilizer mixture `m` has
`|m_v - (1+c) <psi|D(v)|psi>| <= c` for all `v`, with `c_d >= sup_psi c(psi)`. The modulus
is replaced by a 16-gon, which gives lower and upper values. Local search over `psi` gave:

| `d` | `n` | best `c(psi)` (lower, upper) | `d/pi` |
|---|---|---|---|
| 3 | 1 | 0.7500, 0.763 | 0.955 |
| 3 | 2 | 0.7492, 0.7564 | 0.955 |
| 5 | 1 | 1.3843, 1.3940 | 1.592 |
| 7 | 1 | 2.0475, 2.0668 | 2.228 |

The exact pair gap `eps_d = min(delta_u + delta_v)` over non-commuting Weyl pairs is
`0.586, 0.634, 0.517, 0.398, 0.266, 0.227` for `d = 2, 3, 5, 7, 11, 13`, about `3/d` for large `d`.

## Attempts

1. *Pair-threshold averaging* (`qudit-weyl-rounding-constant-linear-upper-bound-proof`).
   This proves `2/sin(pi/d) + 3`, and with the numerical exact pair gap it would give about
   `2d/3`. It dies at a factor of about 2 above the Harper bound. The hard threshold charges
   every term with `delta >= tau` at rate `1/tau - 1`, while the Harper example has all its
   frustration spread over terms with `delta` near `pi/d`.
2. *Post-selection, as in `qudit-code-rounding-factor-one-plus-inv-sqrt-d-proof`*
   (sketch, not a proof). Post-select the top eigenvector `psi` on the eigenspace `P` of
   the best term `u_R`. Terms that do not commute with `u_R` have `P u P = 0`, so they drop
   out with their weight `L`, and commuting terms give a smaller instance on `P`. The
   induction closes with constant `c` whenever the leak
   `<psi|K|psi> - <psi_1|K|psi_1>` is at most `(c/(1+c)) L`. For `c = d/pi` that means
   `kappa = 1 - pi/d + O(d^(-2))`. It dies at the leak estimate. Cauchy–Schwarz gives only
   `sqrt((1-M)/M)` per unit weight, with `M = <psi|P|psi>`, and
   `1 - M <= delta_R/(1 - cos(2pi/d))`. That is useful only when `delta_R = O(d^(-2))`,
   while the pair bound guarantees nothing below `pi/d`. A Jordan-type lemma is needed for
   the pair `(P, u)`, where `u` permutes the `d` eigenspaces of `u_R` cyclically. The
   leak there is governed by a `d`-cycle (Harper) spectrum, not by two-dimensional blocks.

3. *Harper-spectral upper bound toward `d/pi`* (w3-078, 2026-09-18). This dies because the
   target is false. The aim was a leak lemma whose per-term defect is the Harper gap `2pi/d`. So
   the first question was which one-qudit configuration of directions has the smallest semiclassical
   frustration per unit of stabilizer loss.
   - In the small-angle regime, `F_min ~ (pi/d) ||D Omega D||_1` and `F_stab <= 2(W - m_iso)`.
     Here `Omega` is the integer symplectic Gram matrix of the directions, `D = diag(sqrt w)`, and
     `m_iso` is the maximum weight of a commuting set.
   - So `c ~ (d/2pi) rho` with `rho = 4(W - m_iso)/||D Omega D||_1`. The square Harper sum has
     `rho = 2`, which is the source of `d/pi`.
   - The triangle `Z, X, e^(i pi/d) XZ` has `rho = 4/sqrt3`, which gives `2d/(sqrt3 pi)`. For one qudit
     the Farey graph is `K_4`-free, and Motzkin–Straus caps `rho` at `4/sqrt3` (heuristic, small-angle
     regime).
   - The triangle bound is proved in `qudit-weyl-rounding-constant-triangular-harper-bound`, with a
     chirped Gaussian and Poisson summation. The phase `e^(i pi/d) = -omega^(2^(-1))` is essential,
     because `+D(1,1)` is frustrated and gives `c ~ 0.2`.
   - So `c_d >= 2d/(sqrt3 pi) - 1 - o(1)`, and the conjecture above is refuted.

   What survives: the leading coefficient lies in `[2/(sqrt3 pi), 2/pi]`. The natural replacement
   conjecture is `c_d = 2d/(sqrt3 pi) + O(1)`. A matching upper bound would need two things:
   - a quantum uncertainty bound `F >= (pi/d) ||D Omega D||_1 (1 - o(1))` for the non-negligible
     terms;
   - a rounding that loses only `2(W - m_iso)`.

   The antiparity example at `d = 3` shows that the small-angle picture is not the whole story for
   small `d`.

**What is missing.**
1. The leak lemma in Attempt 2. The Harper example suggests that the per-term defect is
   the Harper gap `2pi/d`.
2. Whether the one-qudit optimum persists for `n >= 2`. At `d = 3`, `n = 2` it does
   (0.749 against 0.75). For `d >= 5`, `n = 2` it is untested.
3. An exact one-qudit value for `d = 5, 7`, i.e. the extremal `K` recovered from the LP dual.
