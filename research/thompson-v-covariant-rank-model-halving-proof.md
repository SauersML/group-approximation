---
rg: 2
id: thompson-v-covariant-rank-model-halving-proof
kind: route
title: Halve the rank of a cylinder idempotent with prefix replacements
target: thompson-v-cantor-system-has-no-covariant-rank-model
requires: []
artifacts:
  - research/artifacts/thompson-v-rank-models-cantor-covariance-2026-09-12.md
---

The proof is Section 2 of the artifact.

- **Lemma 2.1.** In a matrix rank ultraproduct, conjugation by units preserves rank, and orthogonal
  idempotents have additive rank. The second is proved at finite stages from representatives that are
  approximate idempotents.
- **Lemma 2.2.** `V` acts transitively on proper nonempty clopen sets: refine both cylinder
  decompositions to equal counts, then map cylinders to cylinders by one prefix replacement.
- **Theorem 2.3.**
  - Put `mu(A) = rk(rho(1_A))`. Covariance gives `mu(gA) = mu(A)`, and additivity gives
    `mu([0]) = mu([00]) + mu([01])`.
  - By transitivity all three values are equal, so `mu([0]) = 0`, and likewise `mu([1]) = 0`.
  - This contradicts `mu(X) = rk(1) = 1`.
- **Proposition 2.4.** Running the same computation with defects for `h_1, ..., h_4` gives
  `1 <= 4 eps`.
