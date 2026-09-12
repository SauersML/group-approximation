---
rg: 2
id: el3-rank-triviality-via-defect-piece-covariance
kind: route
title: A violation of the two-root identity would put a covariant diagonal on the defect piece, which the halving obstruction forbids
target: leavitt-el3-rank-models-over-finite-fields-are-trivial
requires: [leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model, leavitt-two-root-defect-piece-forces-covariant-diagonal, thompson-v-cantor-system-has-no-covariant-rank-model]
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

Artifact Section 3. Characteristic two only.
1. Suppose a char-2 rank model of `R^x` violates `N_23 N_12 = 0`. By corner locality its corner pair has
   `delta > 0`.
2. By the first two requirements, the defect piece carries covariant orthogonal cylinder idempotents of
   positive rank.
3. By the third requirement they cannot exist, since all proper cylinders would share one rank `c` with
   `c = 2c`.
4. So the identity holds in every char-2 model, which is the target in characteristic two.
