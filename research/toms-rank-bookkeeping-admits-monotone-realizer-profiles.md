---
rg: 2
id: toms-rank-bookkeeping-admits-monotone-realizer-profiles
kind: claim
title: In Toms's tower the fibre-rank data of a Cuntz-increasing realizer of a non-constant continuous rank can always be written down, so slack counting alone cannot refute it
distinct_from:
  doubling-ah-finite-stage-continuous-ranks-are-constant: that shows a single finite-stage element, or an orthogonal sum of them, has constant continuous rank; this shows that a Cuntz-increasing sequence of finite-stage profiles meets every rank-level constraint for a non-constant target.
  cuntz-sups-with-continuous-rank-converge-uniformly: that proves the uniform sandwich a realizer must satisfy; this exhibits profiles satisfying the sandwich together with pointwise superadditivity under pushforward.
  toms-schubert-algebra-continuous-ranks-are-constant: that is the rigidity conjecture; this is a firewall on one proof strategy for it, the rank-slack exhaustion at all-wall points.
---

Let `A = lim (A_N, phi_N)` be the non-simple limit of Toms's Section 4
(arXiv:2606.12188v2): `X_(N+1) = X_N x X_N x CP^(j_N)`, unit `q_N` of rank
`r_N = d_N = 2^(N-1) d`, and `p_N in M_k(A_N)` the pushforward of `theta^d`.
For `M > N` the composite `phi_(N,M)` is a sum over `M' = 2^(M-N)` copies
`z -> z^(i)` (composites of coordinate projections), each twisted by a line
bundle. Fix `h in C(X_1)` with `0 <= h <= 1` and put `f(tau) = tau(h)` and
`F_N(x) = 2^(1-N) sum_l h(x_l)` for `x in X_N`, the average over leaves.

**Rank constraints of a realizer.** Suppose `a_n in M_k(A_(N_n))_+` form a
Cuntz-increasing sequence (with `phi(a_n) <~ a_(n+1)` at stage `N_(n+1)`) whose
ranks converge uniformly to `f`. Their fibre-rank functions `R_n` satisfy:
- (C1) `R_n` is lower semicontinuous and integer-valued, `0 <= R_n <= k r_(N_n)`;
- (C2) `sum_i R_n(z^(i)) <= R_(n+1)(z)` for every `z in X_(N_(n+1))`;
- (C3) `sup_tau | integral R_n / r_(N_n) d mu_(N_n) - f(tau) | -> 0`, where
  `mu_N` is the stage-`N` measure of `tau`.

**Theorem.** Put `N_n = n` and `R_n = max(0, ceil(r_n F_n - 2))`.
1. `(R_n)` satisfies (C1)–(C3), with the pointwise sandwich
   `F_n - 2/r_n <= R_n / r_n <= F_n`.
2. Each `R_n` is the rank function of an explicit positive element of
   `p_n M_k(A_n) p_n`: a ramp through a fixed ordering of the `r_n` orthogonal
   line subbundles `theta tensor gamma_l` of `p_n`.
3. At every point `z` where every copy `z^(i)` sits on a wall of `R_n` (a point
   of the locus `r_n F_n - 2 in Z`), `R_(n+1)(z) >= sum_i R_n(y_i)` for points
   `y_i` just across the walls. So all walls are pushed away at once, and the
   next stage has its own walls elsewhere.

**Consequence.** An obstruction that reads only fibre ranks of approximants
(integrality, lower semicontinuity, superadditivity under pushforward and the
uniform sandwich) cannot refute a non-constant continuous rank. The slack
at stage `n` is about `2/r_n` per unit, while one wall jump costs `1/r_n`, so
slack never runs out. Any refutation must use the operators that implement
`phi(a_n) <~ a_(n+1)`: the transports carrying old support into new support
across twisted copies. That is where
`toms-twisted-swap-pairs-are-totally-degeneracy-forcing` acts.

**Model test.**
- *The target matters.* With `h` constant the profiles are constant, and the
  theorem is the trivial realization of a constant rank.
- *Load-bearing count.* Superadditivity (C2) uses `M' >= 2` copies per step:
  `sum_i ceil(g_i - 2) < sum_i g_i - M' <= ceil(sum_i g_i - 2)`. The offset `2`
  is the smallest integer that works for `M' = 2`.
- *Real object.* Toms's tower. The data ignore the twists entirely, so the
  same data serve the untwisted tower, which is the point of the firewall.

Proof: `toms-rank-bookkeeping-monotone-profiles-proof`. Elementary internal
derivation, unreviewed.
