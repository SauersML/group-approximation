---
rg: 2
id: fpbs-cycle-tail-compactness-via-length-canonical-covers
kind: route
title: Prove cost-Betti for finitely presented groups, pass to finitely generated groups along length-canonical covers, and read tail compactness from the cycle identity
target: fpbs-bernoulli-cycle-tail-compactness
requires:
  - fpbs-cost-betti-for-finitely-presented-groups
  - fpbs-bernoulli-cost-lsc-along-length-canonical-covers
  - fpbs-cost-betti-fg-iff-fp-and-length-canonical-cost-lsc
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
---

Written derivation. Artifact, Section 4.

1. The two open inputs and part (1) of the established reduction give `C(b_G) = 1 + beta_1(G)` for every infinite
   finitely generated `G`.
2. Finite-window certificates give bounded-degree graphings `Phi_n` with `c(Phi_n) -> C(b_G)`. See
   `fpbs-bernoulli-cost-usc-on-marked-groups`, Step 2.
3. By the identity, `z(Phi_n) = c(Phi_n) - 1 - beta_1 -> 0`. So `0 <= z - z_L <= z` forces the double limit to vanish.

This route cannot be replaced by one over arbitrary finitely presented covers. See
`fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers`.

This is dependency bookkeeping, not formal verification.
