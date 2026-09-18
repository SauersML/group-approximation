---
rg: 2
id: cmsz-pg22-level-one-block-h1-certificate
kind: route
title: Exact rank certificate for H^1 of the level-zero and level-one block square complexes, then the rank-two H^1 criterion
target: cmsz-pg22-level-one-block-recodings-admit-no-brick-coding
requires:
  - two-graph-brick-codings-die-when-square-complex-h1-has-rank-two
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
  - experiments/nv-conformal-rigidity-2026-09-17/block_h1.py
  - experiments/nv-conformal-rigidity-2026-09-17/run_block_h1.py
  - experiments/nv-conformal-rigidity-2026-09-17/block_h1_pg22_k1.log
  - experiments/nv-conformal-rigidity-2026-09-17/product_control.log
  - experiments/nv-brick-coding-2026-09-17/tp_q2.json
  - experiments/nv-brick-coding-2026-09-17/rs2graph.py
  - experiments/nv-brick-coding-2026-09-17/tp.py
  - experiments/nv-brick-coding-2026-09-17/certificate.py
---

Details: Section 4 of the artifact. To reproduce, run
`SLOW_MAX=0 python3 run_block_h1.py 1 5` in `experiments/nv-conformal-rigidity-2026-09-17/`,
which writes `block_h1_pg22_k1.log`. It takes a few minutes.

1. **Build.**
   - `rs2graph.build(T)` gives `Λ_T`, and `tp.check` verifies (A1)–(A3).
   - `block_h1.grids` enumerates the `(a,b)`-rectangles by filling grids through the square
     relation. The counts are `V = 42, 672`, `E = 336, 5376`, `F = 672, 10752` at
     `k = 0, 1`.
2. **Upper bound.** `h1_fast` gauge-fixes a spanning tree (the script asserts the 1-skeleton
   is connected), then applies exact substitutions `x = 0` and `x = ±y`. It eliminates the
   remaining relations over `GF(1000003)`, so `rank_{GF(p)} ≤ rank_Q` and the result is an
   upper bound for `dim_Q H^1`.
   - It returns 2 for every `T` at `k = 0` and `k = 1`.
   - At `k = 0` it is cross-checked against the plain elimination `h1_level`. That value 2
     agrees with the independent `certificate.py` bound in
     `cmsz-pg22-no-brick-coding-certificate`.
3. **Lower bound.** `[d_1]` and `[d_2]` are independent, because a coboundary sums to 0
   around closed monochromatic cycles and `d_j` does not. So the dimension is exactly 2.
4. **Criterion.** `M_1` of `Λ_T` is primitive with row sums 4, so `ρ(M_1) = 4 > 1`, as
   exactly checked in `cmsz-pg22-no-brick-coding-certificate`. Apply
   `two-graph-brick-codings-die-when-square-complex-h1-has-rank-two`: (a) to `Λ_T` and (b)
   with `k = 1` to `Λ_T^{[1]}`.
5. **Control** (not needed for the proof). The product of two full 4-shifts gives
   `26, 98, 386` at `k = 0, 1, 2`, which is `2 + 24·4^k`, so the method detects growth.

**Trust base.** The Python scripts, with no independent second implementation at
`k = 1`. The fast and plain methods agree at `k = 0`.
