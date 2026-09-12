---
rg: 2
id: two-root-identities-localize-proof
kind: route
title: Diagonal compression is a ring map on block triangular matrices, block ranks add, and matrix units on the diagonal kill the model
target: two-root-identities-localize-to-diagonal-blocks
requires:
  - flag-preserving-rank-models-of-el3-reduce-to-their-diagonal
  - el3-unit-root-matrix-units-iff-two-root-identities
  - matrix-unit-rank-models-extract-ring-rank-models
artifacts:
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Artifact Section 4.4, Proposition 9.

1. **Descent.** Root displacements have block triangular representatives, and so does any
   polynomial in them. `D_i` is additive and multiplicative on block triangular matrices, with
   `D_i(1) = 1`, so `D_i(P(N_i)) = P(D_i(N_i))`. Rank contraction (Lemma 6.2) gives
   `rk(P(N^D)) <= rk(P(N))`.
2. **Additivity.** A block diagonal matrix has rank equal to the sum of its block ranks.
3. **Localized gate.** Weighted-average block identities give `N^D_12^2 = 0` and
   `N^D_23 N^D_12 = 0` in `M`. Then:
   * the diagonal model's unit roots act by matrix units
     (`el3-unit-root-matrix-units-iff-two-root-identities`);
   * a nonzero `p_1` would extract a ring rank model
     (`matrix-unit-rank-models-extract-ring-rank-models`), which the hypothesis forbids, so the
     diagonal model is trivial;
   * `sigma` is then trivial by `flag-preserving-rank-models-of-el3-reduce-to-their-diagonal`.
