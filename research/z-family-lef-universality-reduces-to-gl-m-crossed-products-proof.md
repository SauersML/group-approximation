---
rg: 2
id: z-family-lef-universality-reduces-to-gl-m-crossed-products-proof
kind: route
title: Reduction of Z-family LEF universality to GL_m over subshift crossed products, via Ore, Whitehead and towers
target: z-family-lef-universality-reduces-to-gl-m-crossed-products
requires:
  - rf-groups-lie-in-derived-subgroups-of-rf-groups
  - tower-subshift-elementary-group-is-el-3k-of-base
artifacts:
  - research/artifacts/sk-lef-embedding-d-z-family-2026-09-13-part1.md
---

(i) ⇒ (ii) holds because `G_Y ≤ GL_3(R_Y)`.

(ii) ⇒ (i). Let `Γ` be f.g. LEF.
1. Take `Γ ≤ [Δ,Δ]` with `Δ` f.g. LEF (required claim, part 2), and `ρ : Δ -> GL_m(R_X)` injective.
2. Put `S = M_m(R_X) ≅ R_(X^(m))` (tower claim, items 1–2), so `EL_3(S) ≅ G_(X^(m))`.
3. Whitehead's lemma over any unital ring gives `diag(c,c^{-1}) ∈ E_2(S)` for `c ∈ S^×`.
4. The identity `diag(a,a^{-1},1)diag(b,b^{-1},1)diag((ba)^{-1},ba,1) = diag([a,b],1,1)` then gives
   `diag([a,b],1,1) ∈ EL_3(S)`.
5. `c ↦ diag(c,1,1)` is an injective homomorphism `S^× -> GL_3(S)` carrying `[S^×,S^×]` into `EL_3(S)`. Restricting
   it to `ρ(Γ) ⊆ [ρ(Δ),ρ(Δ)]` embeds `Γ` in `G_(X^(m))`.
