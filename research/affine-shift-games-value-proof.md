---
rg: 2
id: affine-shift-games-value-proof
kind: route
title: Bound common satisfied neighbors by polynomial roots and count pairs of edges
target: affine-shift-games-have-vanishing-value
requires: []
artifacts:
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - scripts/check_unique_games_affine_soundness.py
  - research/artifacts/unique-games-affine-test-replay-2026-09-07.json
---

Section 2 gives the complete construction and proof. If two left vertices
with labels `a_u,a_v` both satisfy their edges at `b`, then
`(u+v)b^2` equals either `a_u+a_v` or `a_u+a_v+b`. Since `u!=v`,
the first equation has at most one root and the second at most two.
Every pair of distinct left vertices thus has at most three common
satisfied right neighbors.

Writing `d_b` for the satisfied degree gives
`sum_b binom(d_b,2)<=3 binom(N,2)`. Cauchy--Schwarz implies
`N s^2<=s+3` for the satisfied fraction `s`. Solve the quadratic
and use `s<=1` to obtain both stated bounds. The fibers of the explicit
projection are the required affine pairs. Section 2 also proves the
value-preserving regular cloning.

The exact checker exhausts the polynomial count over four small finite
fields and the complete labeling optimization at `N=4`. The general
theorem is proved mathematically; it is not inferred from those checks.
