---
rg: 2
id: nonsofic-leavitt-el4-non-uniform-exponential-growth-proof
kind: route
title: The Leavitt matrix units s_i t_j give L ≅ M_2(L), and the self-similar ring theorem applies
target: nonsofic-leavitt-el4-non-uniform-exponential-growth
requires: [self-similar-ring-elementary-groups-non-uniform-growth, universal-leavitt-el4-nonsofic]
artifacts:
  - research/artifacts/sk-free-8-nonuniform-growth-2026-09-13-part2.md
---

1. **Matrix units.** Put `ε_ij = s_i t_j` for `i,j ∈ {0,1}`. From `t_j s_k = δ_jk`, `ε_ij ε_kl = δ_jk ε_il`, and `ε_00 + ε_11 = 1`. So `L ≅ M_2(ε_00 L ε_00)`.
2. **The corner.** `a ↦ s_0 a t_0` is a ring isomorphism `L → ε_00 L ε_00`:
   - multiplicative: `s_0 a t_0 s_0 b t_0 = s_0 ab t_0`;
   - unital: it sends 1 to `ε_00`;
   - injective: `t_0 (s_0 a t_0) s_0 = a`;
   - onto: `ε_00 x ε_00 = s_0 (t_0 x s_0) t_0`.
   Hence `L ≅ M_2(L)`.
3. **Hypotheses.** `L` is generated as a ring by 4 elements and has characteristic 2. `EL_n(L)` is infinite (`e_12(r)` for distinct `r ∈ L`). Apply `self-similar-ring-elementary-groups-non-uniform-growth`.
4. **Nonsoficity.** Nonsoficity with (T) for `EL_4(L)` is the established, kernel-checked `universal-leavitt-el4-nonsofic`. Check that the "universal binary Leavitt algebra" there is this `L` over `F_2`; its node names `BinaryLeavittAlgebra (ZMod 2)`.
