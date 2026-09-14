---
rg: 2
id: rank-four-subshift-groups-see-rational-spectrum-proof
kind: route
title: Type rigidity makes every approximant a ring model, idempotent ranks give divisibility, and prime-twisted periodic models give sharpness
target: rank-four-subshift-groups-see-rational-spectrum
requires: [el-rank-four-finite-simple-shadows-are-ring-models, subshift-group-model-sizes-see-rational-spectrum]
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part4.md
---

Full proof: artifact part 4 §2.
- **Div ⊇.** Every approximant is `PSL_(N d_k)(F_(2^f))` with a ring model `ρ_k`. The idempotents of a cyclic factor of
  order `c` are finitely many ring relations, killed for large `k`, so `c | d_k`.
- **Div ⊆.**
  - Periodic ring models of sizes `d_k = g_(r_k) p_k` and `d′_k = g_(r_k) p′_k`, with distinct primes, converge to
    `G_X^(N)`.
  - `m | N g_(r_k) p_k` and `m | N g_(r_k) p′_k` give `m | N g_(r_k)`.
- **Invariance.** A change of generating set preserves converging sequences, and the natural dimension of `PSL_M(F_q)`
  is well defined for large `M`.
- **Recovery.** `Div` determines the supernatural `N·g_∞(X)`, hence `Cyc(X)` for fixed `N`.
