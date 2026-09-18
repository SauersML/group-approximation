---
rg: 2
id: gaussian-universe-discretises-to-robust-rich-2to1-sdp-gaps
kind: claim
title: For every n >= 2 and eta > 0 there are d and a finite weighted rich 2-to-1 instance with alphabets [2n], [n] whose basic SDP value is at least 1 - eta and whose integral value is at most val(Gamma_(n,d)) + eta, obtained from polar frames of the Gaussian pair-sum universe
distinct_from:
  rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps: that discretises the Haar-frame game U_n, whose SDP solution is exactly perfect at every point; here the Gaussian game has no exactly perfect solution, and the polar-frame vectors only reach 1 - eta after d is taken large. The cells are cells of the polar frames.
  walsh-frame-rich-2to1-games-have-value-near-one: that concerns Walsh-framed finite solutions; this concerns a discretised Gaussian universe.
artifacts:
  - experiments/gaussian-rich-2to1-universe-2026-09-17/check_gaussian_universe.py
---

**ESTABLISHED.** Proof: route `gaussian-universe-polar-frame-discretisation-proof`.

The game `Gamma_(n,d)` is defined in
`gaussian-universe-rich-2to1-game-has-vanishing-value`. The basic SDP is
GKOPTW Figure 1, as quoted and audited in
`rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps`. Its
constraints are only unit total norm per vertex and orthogonality within a
vertex. There is no nonnegativity constraint.

**Polar-frame solution.** For `d >= 2n`, `G` has full column rank almost
surely. Put `polar(G) = G (G^T G)^(-1/2)`, a `d x 2n` matrix with orthonormal
columns. The SDP vectors are

`z(G, a) = polar(G)_a / sqrt(2n)` and `z(H, b) = polar(H)_b / sqrt(n)`.

With `Sigma = G^T G / d`, the objective at an edge `(G, H = G M_P, P)` is

`o(G, P) = (1/(sqrt2 n)) sum_a [ Sigma^(1/2) M_P (M_P^T Sigma M_P)^(-1/2) ]_(a, P(a))`.

**Theorem.**

1. `E o(G, P) -> 1` as `d -> infinity` with `n` fixed.
2. For every `n >= 2`, `d >= 2n` and `eps > 0`, there is a finite weighted rich
   2-to-1 instance with alphabets `[2n], [n]` whose basic SDP value is at
   least `E o - 2 sqrt2 eps - eps` and whose value is at most
   `val(Gamma_(n,d)) + eps`.

**Computation.** At `n = 3`, the artifact estimates `E o` by Monte Carlo
(seed `20260917`, 400 trials per row):

| `d` | 6 | 24 | 96 | 384 | 1536 |
|---|---|---|---|---|---|
| `E o` | 0.878 | 0.982 | 0.996 | 0.9991 | 0.9998 |

The deficit is roughly proportional to `1/d`.
