---
rg: 2
id: lef-growth-of-subshift-el-groups-is-monotone-under-factors-proof
kind: route
title: The pullback ring map gives a Lipschitz embedding of balls, and local models restrict
target: lef-growth-of-subshift-el-groups-is-monotone-under-factors
requires: []
artifacts: [research/artifacts/sk-lef-growth-all-towers-2026-09-13-part3.md]
---

1. **Ring map.** Π(Σ f_j u^j) = Σ (f_j∘π) u^j is an injective ring homomorphism R_Y → R_X. It is equivariant because π∘T_X = T_Y∘π.
2. **Group map.** It induces an injective homomorphism G_Y → G_X with e_ij(r) ↦ e_ij(Π r).
3. **Distortion.** The generators e_ij(1) and e_ij(u^{±1}) map to generators. The generator e_ij(e_b) maps to e_ij(e_{π^{-1}[b]}), of some length K_{ij,b}. With K = max(1, K_{ij,b}), B_Y(r) maps injectively into B_X(Kr).
4. **Restriction.** An injective partial homomorphism φ of B_X(Kr) restricts along Π to one of B_Y(r), because Π(gh) = Π(g)Π(h) stays in B_X(Kr). So L_Y(r) ≤ L_X(Kr).

Details: artifact part 3, Theorem M.
