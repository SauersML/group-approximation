---
rg: 2
id: o2-ideal-projection-unit-witness-fails-cancellation-proof
kind: route
title: Compress the witness to a full projection corner and use cancelled room to absorb the stabilization
target: o2-ideal-projection-unit-witness-fails-cancellation
requires: []
artifacts:
  - research/artifacts/k1-o2-ideal-finite-nuclear-dimension-2026-09-13.md
---

Complete proof in the artifact, section 4 (Proposition 6 and Corollary 7).

- **Compression.** `u = 1 + x` is homotopic to `v + (1 - p_n)`, with `v` a unitary of the full corner
  `p_n I p_n`.
- **K-theory.** Brown's theorem makes `K_1(p_n I p_n) -> K_1(I)` bijective, so `v ⊕ 1_k` is null in
  `M_{k+1}(p_n I p_n)`.
- **Transport.** Partial isometries onto `k` orthogonal copies of `p_n` below `p_m - p_n` carry that
  null-homotopy into `Ĩ`.
- **Room from O_2.** The projections `S_w p_n S_w^*` with `|w| = j` sit approximately below `p_m`, so
  `2^j[p_n] <= [p_m]`. Order cancellation yields `(2^j-1)[p_n] <= [p_m - p_n]`.
