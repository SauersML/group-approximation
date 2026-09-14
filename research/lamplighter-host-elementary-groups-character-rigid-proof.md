---
rg: 2
id: lamplighter-host-elementary-groups-character-rigid-proof
kind: route
title: UHF unit groups, normalizing diagonal units, and tower algebras conjugated into the UHF algebra by the Bernoulli measure
target: lamplighter-host-elementary-groups-are-character-rigid
requires: []
artifacts:
  - research/artifacts/sk-lamplighter-characters-2026-09-14-part1.md
  - research/artifacts/sk-lamplighter-characters-2026-09-14-part2.md
---

Complete derivation in the artifacts. It follows the reviewed Z-case (`subshift-elementary-groups-character-rigid-proof`), with three replacements.

1. **UHF unit group.** The lamp subgroup `K = ⊕_Δ F_2` acts freely, and `R_K = LC(Ω,F_2) ⋊ K = ⋃_W M_{2^{|W|}}(F_2)` with inclusions `x ↦ x⊗I`. So `L = GL_n(R_K) = ⋃ GL_{n2^{|W|}}(F_2) ⊆ G_Δ` is a single-block diagonal limit: a nontrivial `h` has support at least `N_k/N_m` at every later stage. Larsen–Tiep decay then makes every character constant off `1` on `L`, on its conjugates by normalizing elements, and on `wLw^{-1}` for units `w`.
2. **Generation and the central part.** `d_δ = diag(u_δ,1,…,1)` normalizes `G_Δ`, and `G_Δ = ⟨L, d_δ^{±1}Ld_δ^{∓1}⟩`. All these subgroups contain `A' = e_23(LC(Ω,F_2))`. Equal traces give `p_L = p_{A'} = p_{dLd^{-1}}`, so `p_{A'}` is central and `χ = c + (1−c)χ_2`.
3. **Bessel step.**
   - For `g ≠ 1`, take far-apart small sets `V_k` (topological freeness) with noncommuting roots `x_k`, and the finite tower groups `H_{V_k} ∋ x_k, g^{-1}x_kg`.
   - The Bernoulli measure is Λ-invariant, so the idempotents `e_{aV_k}` have equal ranks in a UHF stage. The tower matrix units `e_{aV_k}u_{ab^{-1}}` are therefore conjugate by one unit `w` to matrix units of `R_K`, with `w` trivial on the complement.
   - So `∏H_{V_k} ⊆ wLw^{-1} ⊆ G_Δ`. That group shares `e_23((1−e)LC(Ω))` with `L`, so `χ_2` vanishes off 1 there.
   - The vectors `π(x_kgx_k^{-1})ξ` are orthonormal, and Bessel gives `χ_2(g) = 0`.
