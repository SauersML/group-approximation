---
rg: 2
id: gaussian-pair-sum-universe-rich-2to1-game-has-vanishing-value
kind: claim
title: The Gaussian pair-sum universe W_(n,d) is a rich 2-to-1 game whose polar-orthonormalised basic SDP solution has objective tending to 1 as d grows at fixed n, while its integral value is at most 4^(1/4) ((2n)^(-kappa) + eps_n)^(1/160) uniformly in d
distinct_from:
  rotated-frame-universe-rich-2to1-game-has-vanishing-value: that is the vanishing-value question for the Haar-frame universe U_n, whose SDP solution is exactly perfect; this is a different universe (i.i.d. Gaussian rows, pair sums) whose SDP solution is only asymptotically perfect as d grows, and its value is proved to vanish. It does not decide the Haar-frame question.
  rotated-frame-value-reduces-to-partition-stability: that proves val^4 <= 4 Stab_T(rho_A) for Haar frames; this reuses the same five steps in the Gaussian model, where the stability bound is proved.
  walsh-frame-rich-2to1-games-have-value-near-one: that shows Walsh-framed perfect SDP solutions force value near 1; this is a perfect-in-the-limit SDP universe with value near 0.
artifacts:
  - experiments/gaussian-pair-sum-universe-2026-09-17/check_gaussian_universe.py
---

**ESTABLISHED.** Proof: route `gaussian-pair-sum-universe-value-proof`.

## The game W_(n,d)

Fix `n >= 2` and `d >= 1`.

* **Left vertices.** `X = (x_1, ..., x_(2n))`, i.i.d. rows `N(0, I_d / d)`.
* **Edges.** A uniform labelled 2-to-1 map `P : [2n] -> [n]`, independent of `X`.
* **Right vertex.** `Y = Pi_P X`, `y_b = sum_(a in P^(-1)(b)) x_a`.
* **Constraint.** Left label `a` and right label `b` satisfy the edge iff `P(a) = b`.

`val(W_(n,d)) = sup_(A,B) Pr[P(A(X)) = B(Y)]` over Borel `A : R^(2n x d) -> [2n]`
and `B : R^(n x d) -> [n]`.

## Statement

1. **Rich.** For each fixed `P`, the rows of `Y` are i.i.d. `N(0, 2 I_d / d)`.
   So `law(Y)` does not depend on `P`, `P` is uniform given `Y`, and `P` is
   uniform given `X`. The pairing law is uniform at every left and right vertex.
2. **SDP.** For `d >= 2n` let `U(Z) = (Z Z^T)^(-1/2) Z` (polar factor, defined
   a.s.). Put `z(X, a) = U(X)_a / sqrt(2n)` and `z(Y, b) = U(Y)_b / sqrt(n)`.
   These satisfy both GKOPTW Figure 1 constraints exactly. The objective
   `Obj_(n,d) = E sum_a <U(X)_a, U(Y)_(P(a))> / (n sqrt 2)` lies in `[-sqrt2, sqrt2]`
   and tends to `1` as `d -> infinity` at every fixed `n`.
3. **Value.** With `kappa`, `eps_n` of `gaussian-pair-resampling-partitions-are-unstable`,
   for every `n >= 2` and every `d >= 1`,
   `val(W_(n,d)) <= 4^(1/4) ((2n)^(-kappa) + eps_n)^(1/160)`.
   The right side tends to `0` as `n -> infinity` and does not depend on `d`.

## What it changes

This is the value half of a basic-SDP gap universe, proved. Together with the
discretisation in `robust-basic-sdp-gaps-from-gaussian-pair-sum-universe` it
closes `rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps`. The order of
limits is the point: `n` is fixed by the soundness alone, and then `d` absorbs
any completeness defect `eta`. The Haar-frame premise (A1)/(A2) is not needed.

Numerics (artifact): at `n = 4` the SDP objective is `0.960, 0.992, 0.998,
0.9995, 0.9999` for `d = 16, 64, 256, 1024, 4096`. The linear strategy at
`d = 1` has value `0.70, 0.49, 0.33, 0.24, 0.18, 0.15` for
`n = 4, 16, 64, 256, 1024, 4096`.

## Attempts

* **2026-09-18, swarm-0917-w11-w11-ugc-last1 (probability-random): Gaussian
  replacement of the Haar frame. Proved.** The reduction steps are transferred
  one by one, checking the three properties they use; the stability input is
  Theorem G.
