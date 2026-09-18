---
rg: 2
id: gaussian-pair-resampling-partitions-are-unstable
kind: claim
title: In the Gaussian model, every frame-sum-balanced fractional partition of 2n Gaussian vectors has pair-resampling stability at most ((2n)^(-kappa) + eps_n)^(1/40) with absolute kappa > 0 and eps_n -> 0, uniformly in the dimension d, because the 40-fold walk is a Mehler operator whose contraction is strict on 1-perp whenever 40 random matchings form an expander
distinct_from:
  pair-resampling-walk-balanced-partitions-are-unstable: that is the same stability statement for Haar orthonormal frames (d_n >= 2n), where T_P rotates only inside the row space and is not a Mehler operator; this proves the Gaussian-model version, for every d >= 1, and does not decide the frame version.
  rotated-frame-value-reduces-to-partition-stability: that bounds the value of the Haar-frame game by the stability; this bounds the stability itself, in the Gaussian model.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is an algorithmic use of global hypercontractivity; this is a soundness bound that avoids global hypercontractivity altogether by powering the walk.
artifacts:
  - experiments/gaussian-pair-sum-universe-2026-09-17/check_gaussian_universe.py
---

**ESTABLISHED.** Proof: route `gaussian-pair-resampling-partitions-are-unstable-proof`.

## Setting (Gaussian model)

Fix `n >= 2` and `d >= 1`. `G = (g_1, ..., g_(2n))` has i.i.d. standard
Gaussian rows in `R^d`; write `gamma` for its law on `H = R^(2n) (x) R^d`.
For a labelled 2-to-1 map `P : [2n] -> [n]` let `Pi_P` be the orthogonal
projection of `R^(2n)` onto vectors constant on the pairs of `P`, and

* `T_P f = E[f(G) | (Pi_P (x) I) G]`, the conditional expectation onto the pair
  sums `y_b = sum_(a in P^(-1) b) g_a`;
* `T = E_P T_P` (uniform `P`), the pair-resampling walk;
* `s = sum_a g_a`, the frame sum, which every `T_P` keeps.

A *balanced fractional partition* is `rho = (rho_a)_(a in [2n])` with
`rho_a >= 0`, `sum_a rho_a = 1` and `E[rho_a | s] = 1/(2n)`. Every
`S_2n`-equivariant fractional partition is balanced (row permutations preserve
`gamma` and fix `s`). `Stab_T(rho) = sum_a <rho_a, T rho_a>`.

## Statement

**Theorem G.** Put `j = 40`, `h0 = 1/100`, `kappa = h0^2 / (16 j^3) > 9.7e-11`.
There are explicit `eps_n -> 0` (for example `eps_100 < 1e-12`) such that for
every `n >= 2`, every `d >= 1` and every balanced fractional partition `rho`,

```text
Stab_T(rho)  <=  ( (2n)^(-kappa) + eps_n )^(1/40).
```

In particular `sup_rho Stab_T(rho) -> 0` as `n -> infinity`, uniformly in `d`.

## The four steps (proved in the route)

1. **Powering.** `T` is a positive self-adjoint contraction, so
   `Stab_T(rho) <= Stab_(T^j)(rho)^(1/j)` (spectral Holder).
2. **Mehler form.** `T^j = E T_(P_1) ... T_(P_j)` over i.i.d. `P_i`, and
   `T_(P_1) ... T_(P_j)` is the Mehler operator
   `M_D f(x) = E f(D x + (I - D D^T)^(1/2) x')` with
   `D = Pi_(P_j) ... Pi_(P_1)`. `D` fixes the all-ones vector and preserves
   its complement; on each fibre of `s` it acts as `M_(D')`,
   `D' = D restricted to 1-perp`.
3. **Contraction from expansion (Lemma N).** For unit `x` in `1-perp`,
   `||D x||^2 <= 1 - lambda_2(L_H)/(2 j^2)`, where `L_H` is the Laplacian of
   the multigraph `H` formed by the `j` matchings. With Cheeger
   (`lambda_2 >= h(H)^2/(2j)`), `||D'|| <= r0 < 1` whenever `h(H) >= h0`.
   Then `M_(D') = M_(sqrt r) M_E M_(sqrt r)` with `||E|| <= 1`, and Nelson's
   inequality gives `sum_a <rho_a, M_D rho_a> <= (2n)^(-(1-r)/(1+r))`.
4. **Expansion is typical (Lemma E).** `Pr[h(H) < h0] <= eps_n`, by a union
   bound over sets: an exact small-set bound for `|S| <= n/4` and a sequential
   Chernoff bound for `n/4 < |S| <= n`.

## What it changes

* **The recorded obstruction is bypassed, not refuted.** The Attempts of
  `pair-resampling-walk-balanced-partitions-are-unstable` show that `T`
  itself admits no uniform Ornstein--Uhlenbeck domination, because
  `lambda_k >= 1/((2n-1)(2n-3))` at every degree. That floor comes from
  pairing patterns shared by one matching. Under `T^40` the analogous floor is
  the probability that 40 matchings fail to expand, and that is `eps_n`,
  summable against `Stab <= 1`. No level-`k` eigenvalue bound, no global
  hypercontractivity and no `lambda_k <= 2^(-k/2)` conjecture is needed.
* **Uniform in `d`.** The bound holds already at `d = 1`, where the players
  see `2n` real numbers and `n` unlabelled pair sums.
* **Rate.** `kappa` is tiny, so the bound is qualitative. The artifact's
  Monte Carlo of the linear strategy at `d = 1` (value `0.70, 0.49, 0.33,
  0.24, 0.18, 0.15` at `n = 4, 16, 64, 256, 1024, 4096`) decays much faster
  than the proved rate. Better expansion constants (Friedman-type) improve
  `kappa` only to order `1/j`.
* **Consumer.** `gaussian-pair-sum-universe-rich-2to1-game-has-vanishing-value`.

## Attempts

* **2026-09-18, swarm-0917-w11-w11-ugc-last1 (probability-random): powered
  walk on expanding matching unions. Proved.** The artifact checks the exact
  crossing law of a random matching against both tail bounds of Lemma E, the
  union-bound constants (small-regime base `0.0126`, linear base `0.316`,
  both `<= 1/2`), Lemma N on random products (`n <= 40`, `j <= 40`), and the
  Mehler covariance identity `I - D D^T`.
* **Open transfer.** The same powering argument on Haar frames (`d = 2n`)
  needs `L^p -> L^2` smoothing for products of subgroup averages
  `E_(O(W_1)) ... E_(O(W_j))` inside `O(2n-1)`; Nelson is not available there.
  Not attempted.
