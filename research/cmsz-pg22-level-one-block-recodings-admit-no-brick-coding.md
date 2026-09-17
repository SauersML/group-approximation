---
rg: 2
id: cmsz-pg22-level-one-block-recodings-admit-no-brick-coding
kind: claim
title: The level-one higher-block recodings of the five PG(2,2) Robertson-Steger tile 2-graphs have square-complex H^1 of dimension 2 and admit no brick coding in any dimension
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
distinct_from:
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that rules out brick codings of the tile 2-graphs Lambda_T themselves by SAT; this rules out brick codings of their level-one block recodings Lambda_T^[1], the proof uses no SAT.
---

`T0,…,T4` and `Λ_T` are as in `cmsz-pg22-rs-two-graphs-admit-no-brick-coding`. `Λ_T^{[1]}`
is the higher-block 2-graph whose vertices are the 672 rectangles of degree `(1,1)`, whose
edges are the 2688 + 2688 rectangles of degree `(2,1)` and `(1,2)`, and whose squares are
the 10752 rectangles of degree `(2,2)`.

This is survivor (1), block recodings, of the earlier brick-coding artifact, at level 1. The
path space of `Λ_T^{[1]}` is the usual higher-block recoding of that of `Λ_T`, but that
identification is not part of this claim. Neither is any comparison between the brick
codings of `Λ_T` and those of `Λ_T^{[1]}`.

**Claim.** For each `T ∈ {T0,…,T4}`:
- `dim_R H^1(K(Λ_T); R) = 2`;
- `dim_R H^1(K(Λ_T^{[1]}); R) = 2`;
- neither `Λ_T` nor `Λ_T^{[1]}` has a brick coding (B1)–(B3) in any dimension `m ≥ 1`.

Route: `cmsz-pg22-level-one-block-h1-certificate`.
