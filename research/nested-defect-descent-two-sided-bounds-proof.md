---
rg: 2
id: nested-defect-descent-two-sided-bounds-proof
kind: route
title: Restrict each cylinder subgroup to the range of the commuting defects, apply the gap below and square zero above
target: nested-two-root-defect-pieces-decay-geometrically-both-ways
requires:
  - leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
  - leavitt-rank-models-kazhdan-fixed-ideals-are-global
  - leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

Artifact Section 3.

1. **Commuting.** For disjoint cylinders, `iota_A(R^x)` and `iota_B(R^x)` commute. So
   `Q_k = D_(A_1)...D_(A_k)M` is invariant under `sigma(iota_B(R^x))` and under `N^B_12`.
2. **Upper bound.** `N^B_12` is square-zero on `Q_k`, so `rk(D_B q_k) <= rk(N^B_12 q_k) <= f(k)/2`.
3. **Lower bound.**
   * `q_k sigma(iota_B(.)) q_k` is a model on `q_k M q_k`.
   * Globality, transported from `[0]` to `B` by a `V`-element, makes it fixed-point-free.
   * The gap then gives `rk(D_(B1000) q_k) >= c_* f(k)`.
   * `V`-transitivity on disjoint configurations with proper union identifies that rank with `f(k+1)`.
4. **Nested pieces.** `q D_(0P') q = D_(0P') q` identifies the pieces of the defect-piece claim with
   `D_(A_k)...D_(A_1)M` for `A_j = 0^(j-1)1000`.
   * The upper bound needs only commutation and square zero, so it holds in any model.
   * The lower bound passes through the fixed-point-free quotient.
