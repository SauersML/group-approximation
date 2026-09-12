---
rg: 2
id: radu-lattice-defect-idempotents-avoid-finite-subgroups-proof
kind: route
title: Fixed points on the square complex bound finite subgroups, and augmentation or extended characters kill their idempotents
target: radu-lattice-defect-idempotents-avoid-finite-subgroups
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
artifacts:
  - research/artifacts/radu-lattice-binary-algebra-splittings-2026-09-12.md
---

## Why sufficient

Artifact Section 3, Lemma C1 and Proposition C2.
* **Finite subgroups.** A finite subgroup fixes a point of the CAT(0) square complex and permutes the
  vertices of one cell freely, so its order is at most four. The order-four subgroups are the commuting
  rows `(a,x)`, `(a,y)`, `(b,x)`. All of them inject into `(Z/2)^3`.
* **`p = 2`.** Idempotent matrices over the local ring `F_2[H]` are similar to `diag(I_r, 0)`. The
  augmentation turns the corner equation into rank at least `m`. It kills the defect, because a one-sided
  inverse over a field is two-sided.
* **Odd `p`.** Split `F_p[H]` into characters and extend each one to `Gamma_R`. Every component of a corner
  idempotent then has full rank, and every component of the defect vanishes.
