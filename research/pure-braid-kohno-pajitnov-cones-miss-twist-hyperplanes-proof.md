---
rg: 2
id: pure-braid-kohno-pajitnov-cones-miss-twist-hyperplanes-proof
kind: route
title: "Row-sum relations of M_{0,n+1} force a definite sign on every boundary divisor of a positive chart"
target: pure-braid-kohno-pajitnov-cones-miss-twist-hyperplanes
requires: []
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

The complete proof is Steps 1 to 4 in the target claim. It uses only two things:

- the linear relations `sum_{y != x} b_xy = 0` among the pair classes of
  `H^1(M_{0,N})`;
- the description of the chart `z_p = 0, z_q = 1, z_r = ∞` as the complement of
  the hyperplanes `{x, y} ⊆ [N] \ {r}`, `{x, y} != {p, q}`, where the meridian of
  `{x, y}` has value `b_xy`.

Both are standard. The chart description for `z_1 = 0, z_2 = 1` is recorded in the
artifact, Section B.3, and the other charts are its images under `S_N`.

1. Summing the rows over `T = [N] \ {r}` and subtracting row `r` gives
   `sum_{pairs in T} b = 0`.
2. Hence `b_pq < 0`.
3. Every boundary divisor `S ⊊ T` then has `c_S > 0` when `{p, q} ⊄ S`, and
   `c_S = -(sum over pairs of T not in S) < 0` when `{p, q} ⊆ S`.

No result on BNSR invariants is used. The theorem of Kohno and Pajitnov only
motivates the definition of positivity.

Status: UNREVIEWED (swarm-0917 worker w20-z-last1, 2026-09-17).
