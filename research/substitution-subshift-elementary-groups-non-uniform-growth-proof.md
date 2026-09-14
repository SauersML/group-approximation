---
rg: 2
id: substitution-subshift-elementary-groups-non-uniform-growth-proof
kind: route
title: The substitution tower V = ζ(X) gives R_X ≅ M_2(R_X), then apply the self-similar ring theorem
target: substitution-subshift-elementary-groups-non-uniform-growth
requires: [self-similar-ring-elementary-groups-non-uniform-growth, constant-length-substitution-tower-partition, finite-model-subshift-elementary-groups-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-free-8-nonuniform-growth-2026-09-13-part2.md
---

1. **The tower.** By `constant-length-substitution-tower-partition`, `ζ: X → ζ(X)` is a homeomorphism onto a clopen set `V`, `X = V ⊔ TV`, and `ζ∘T = T²∘ζ`. So `(V, T²|_V) ≅ (X,T)`.
2. **`T²V = V`**, since `TV ⊔ T²V = X`.
3. **Matrix units.** `ε_ab ε_cd = δ_bc ε_ad` from `ue_Vu^(−1) = e_(TV)` and `V ∩ TV = ∅`, and `ε_00 + ε_11 = 1`. So `R_X ≅ M_2(e_V R_X e_V)`.
4. **The corner.** Using `(fu^i)(f′u^j) = f(f′∘T^(−i))u^(i+j)`, `e_V(fu^k)e_V = f1_(V∩T^kV)u^k`, which vanishes for odd `k`. So `e_VR_Xe_V = LC(V,F_2) ⋊_(T²) Z` with unit `u²e_V`.
5. **Transfer.** The conjugacy `ζ` induces `R_X ≅ e_VR_Xe_V` via `f ↦ f∘ζ^(−1)` and `u ↦ u²e_V`.
6. **Hypotheses of the ring theorem.** `R_X` is generated as a ring by `u^(±1)` and the letter idempotents `e_([a])`, has characteristic 2, and `EL_3(R_X)` is infinite. Apply `self-similar-ring-elementary-groups-non-uniform-growth`.
7. **Other properties.** Simplicity, (T) and LEF are `finite-model-subshift-elementary-groups-simple-kazhdan-lef` (Z-subshifts have periodic finite models).
