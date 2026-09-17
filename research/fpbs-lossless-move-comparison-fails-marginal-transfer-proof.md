---
rg: 2
id: fpbs-lossless-move-comparison-fails-marginal-transfer-proof
kind: route
title: Rerouting open shortcuts, the exact square and triangular bond thresholds, and two elementary inequalities
target: fpbs-lossless-move-comparison-fails-marginal-transfer
requires:
  - fpbs-generating-set-threshold-comparison
artifacts:
  - experiments/lossless-move-calibration-2026-09-17/thresholds.py
---

Notation as in the target.

## Imports

- **Kesten (1980),** *The critical probability of bond percolation on the
  square lattice equals 1/2*, Comm. Math. Phys. 74, 41–59. So `p_c(Z^2) = 1/2`,
  and for `p < 1/2` Bernoulli bond percolation on `Z^2` has no infinite cluster
  a.s., by the definition of `p_c` and monotonicity of `theta`.
- **Wierman (1981),** *Bond percolation on honeycomb and triangular lattices*,
  Adv. Appl. Probab. 13, 298–313. The critical probability of bond percolation
  on the triangular lattice is `2 sin(pi/18) = 0.347296...`.

## Theorem A

The process `omega^` contains `omega` (it copies the old edges), so each
`omega`-cluster lies inside an `omega^`-cluster. Conversely, let `{x, xt}` be
`omega^`-open. Then some translated path `x -> x u_i -> xt` is `omega`-open.
Replace each open new edge on an `omega^`-open path by that path. The result is
an `omega`-open walk with the same endpoints. So `omega^`-clusters lie inside
`omega`-clusters. ∎

**Properties used in Theorem B.**
- The state of an edge of `Cay(Gamma,T)` is a function of at most `2N` old edges
  inside the ball of radius 2 around its endpoint, the same function at every
  translate. So `omega^` is an equivariant block factor of an iid field, hence
  invariant, ergodic and finite-range dependent.
- It is increasing in `omega`.
- A new edge is closed iff all `N` edge-disjoint paths are closed. These events
  are independent with probability `1 - p^2` each, so the marginal is `m_N(p)`.

## Theorem B

Take `Gamma = Z^2`, `u = e_1`, `v = e_2`, `t = e_1 + e_2`. The two paths
`x -> x+e_1 -> x+t` and `x -> x+e_2 -> x+t` are edge-disjoint, so `N = 2`.
`Cay(Z^2, {±e_1, ±e_2, ±(e_1+e_2)})` is the triangular lattice.

- `m_2(p) = 2p^2 - p^4` is increasing on `[0,1]`. Solving `m_2(p) = q` gives
  `p = sqrt(1 - sqrt(1 - q))`. At `q = 2 sin(pi/18)` this is `0.4382912...`
  (`thresholds.py`).
- For `p ∈ (0.438292, 1/2)`:
  - `m_2(p) > p_c(tri)`;
  - the old-edge marginal is `p > 0.4382 > p_c(tri)`;
  - by Kesten, `omega` has no infinite cluster a.s., so by Theorem A neither
    does `omega^`.
- At `p = 0.44`: `m_2(0.44) = 1 - (1 - 0.1936)^2 = 1 - 0.65028096 = 0.34971904`.

So (LL) would give `p_c(Z^2) <= 0.438292 < 1/2`, contradicting Kesten. The
power-map value `phi_2^{-1}(q) = 1 - (1 - sqrt q)^2` at `q = 0.347296` is
`0.83134...`. ∎

## Theorem C

- `m_N(p) <= N p^2` is Bernoulli's inequality `(1 - x)^N >= 1 - Nx` with
  `x = p^2 ∈ [0,1]`.
- `x -> x^{1/M}` is concave, so it lies below its tangent at `1`:
  `(1 - p)^{1/M} <= 1 - p/M`. Hence `1 - (1-p)^{1/M} >= p/M`, and
  `phi_M(p) >= p^2/M^2`.

So `m_N(p) <= N p^2 <= N M^2 phi_M(p)`. The grid check in `thresholds.py`
returns a maximal ratio `0.99995 <= 1`.

**Window.** (LL) together with `p_u(S) >= p_u(T)` (item 3 of
`fpbs-generating-set-threshold-comparison`) certifies `p_c(S) < p_u(S)` exactly
through `max(p_c(T), m_N^{-1}(p_c(T))) < p_u(T)`. This is equivalent to
`p_c(T) < p_u(T)` and `p_c(T) < m_N(p_u(T))`. Such steps satisfy
`p_c(T) < N M^2 phi_M(p_u(T))`. Steps outside the power-map corollary have
`p_c(T) >= phi_M(p_u(T))`, which gives the stated band. If
`p_c(T) >= N p_u(T)^2 >= m_N(p_u(T))`, the certificate fails. ∎

**Scope.** Theorem B is on an amenable group. It refutes the amenability-blind
marginal principle, not a version restricted to nonamenable groups. The Remark
in the target about `F_2` is a sanity check, not part of the proof.
