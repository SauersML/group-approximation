---
rg: 2
id: level-unit-hnn-extension-rank-models-proof
kind: route
title: Free modules of equal rank give exact intertwiners at every stage of the twisted regular tower
target: level-unit-hnn-extensions-have-anti-central-rank-models
requires: []
artifacts:
  - research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md
---

Section 2 of the artifact: Theorem 2.1, Theorem 2.3, Corollary 2.4, Remark 2.5 and Consequence 2.6.

1. **Tower.** Left multiplication on `F_3[L_j]ε₋` is compatible along `a -> a ⊗ 1_2`. It sends `z` to
   `−1`, and its restriction to a finite subgroup `Γ ∋ z` is free of rank `[L_j : Γ]`. Freeness gives
   injectivity with normalized rank bounded below.
2. **Intertwiners.** Exhaust `B_g` by the finite groups `Γ_i = B_g ∩ L_i`.
   - At stage `j` pick `i(j) -> ∞` with `Γ_i ∪ φ_g(Γ_i) ⊆ L_j`.
   - `F_3[L_j]ε₋` is free of the same rank through `σ_j` and through `σ_j∘φ_g`, so an exact intertwiner
     `X_j` exists.
   - The ultraproduct `[X_j]_ω` intertwines on all of `B_g`.
3. **Extension.** Independent choices for countably many letters give the multiple HNN extension.
4. **Torsion.** When `n | [L_j : Γ_i]` and `Γ_i` is `g`-invariant, transport the free
   `F_3[Γ_i ⋊ <g>]ε₋`-structure. Then `X_j^n = 1`.
