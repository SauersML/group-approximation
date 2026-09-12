---
rg: 2
id: free-rank-models-on-sl3-block-support-proof
kind: route
title: The wrong-order product of two unit root elements is nonzero on free modules and zero under block support
target: free-rank-models-on-sl3-admit-no-block-support
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

Complete proof: artifact Section 4e, Proposition 10 and Example 11.

- **Zero under block support.** If `v_ij = sigma(x_ij(1)) - 1` lies in `p_i M p_j`, then
  `v_23 v_12` lies in `p_2 M p_3 · p_1 M p_2 = 0`.
- **Nonzero on free modules.**
  - `beta = (x_23(1) - 1)(x_12(1) - 1) = hg - h - g + 1` is a combination of four distinct
    elements of `H_0 = SL_3(F_p)`, so `beta != 0` in `k[H_0]`.
  - Left multiplication by `beta` on `k[H_0]` therefore has rank at least `1`.
  - On an invariant summand `k[H_0]^(m_i)` with invariant complement, `sigma_i(beta)` has rank
    at least `m_i`, so `rk(sigma(beta)) >= mu > 0`.
- **Existence.**
  - `S_inf = lim M_(p^k)(F_p)` is a direct limit of simple algebras under unital maps, hence
    simple. Left multiplication on `M_(p^k)(F_p)`, with normalized rank, is a ring rank model.
  - `EL_3(S_inf)` is the union of `EL_3(M_(p^k)(F_p)) = SL_(3 p^k)(F_p)`.
  - The regular representation of `SL_(3 p^k)(F_p)` is exact on that level group and moves
    every nontrivial element with normalized rank at least `1/2`. Along `omega` these give a
    separating model.
  - Its restriction to `H_0` is free of rank `[SL_(3 p^k)(F_p) : H_0]`, so
    `mu = 1/|H_0|`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 34 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
