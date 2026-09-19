---
rg: 2
id: norm-minus-one-sturmian-jm-groups-satisfy-boone-higman-proof
kind: route
title: Rescale the Sturmian interval exchange group into a metallic-mean Stein group, and bound its abelianization by groupoid homology
target: norm-minus-one-sturmian-jm-groups-satisfy-boone-higman
requires: [stein-derived-groups-need-computable-modules]
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

Write `ε = ε_m`, `Γ = Γ_m`, `Λ = ⟨ε⟩`, `V = V(Γ,Λ,N)`.

1. **Units of norm −1 are metallic.**
   - Let `u` be a unit of norm −1 in `K`. Replacing `u` by `±u^{±1}` keeps the norm −1 and gives
     `u ∈ (0,1)`.
   - Its conjugate is `u' = −1/u`, so its trace is `u − 1/u = −m`, with `m = 1/u − u > 0` an integer.
   - So `u² + mu − 1 = 0`, `u = ε_m` and `K = Q(ε_m) = Q(√(m²+4))`.
   - Conversely, `ε_m ε_m' = −1`.
2. **Groupoid homology.** Multiplication by `ε` on `Γ = Z ⊕ Zε` has matrix `A` with `det A = N(ε) = −1` and
   `det(1 − A) = N(1 − ε) = 1 + m − 1 = m`.
   - `H_0 = Γ/(1−ε)Γ` has order `m`.
   - `H_1 = H_2(Γ ⋊ Λ) = H_2(Z² ⋊_A Z)`. The Lyndon--Hochschild--Serre sequence for an extension by `Z`
     gives `0 → H_2(Z²)_A → H_2 → H_1(Z²)^A → 0`.
     - `H_2(Z²) = Z` and `A` acts on it by `det A = −1`, so the coinvariants are `Z/2`.
     - `H_1(Z²)^A = ker(1 − A) = 0`, since `det(1−A) = m ≠ 0`.
     - So `H_1 = Z/2`.
3. **Finite index.** The AH sequence (L) ends with `H_0 ⊗ Z/2 → V^ab → H_1 → 0`. So
   `|V^ab| ≤ 2·gcd(m,2) ≤ 4`.
   - For `m = 1` this gives `|V^ab| ≤ 2`, consistent with Burillo--Nucinkis--Reeves' `V_τ^ab = Z/2`.
   - `D(V)` has finite index, so it is `F_∞` by (C), hence finitely presented, and simple by (S). This proves
     item 1.
4. **Embedding.**
   - Since `Γ = Z ⊕ Zε` spans `K` over `Q`, some `N ≥ 1` has `N·1, Nα ∈ Γ`.
   - `x ↦ Nx` conjugates `IE(Z+Zα)` on `[0,1)` onto the group of right-continuous interval exchanges of
     `[0,N)` with breakpoints and translations in `N(Z+Zα) ⊆ Γ`. These have slope `1 ∈ Λ` and breakpoints in
     `Γ`, so they lie in `V(Γ,Λ,N)`.
   - Taking derived subgroups gives `IE(Z+Zα)' ↪ D(V)`.
   - `IE(Z+Zα) ≅ G_α` (step 3 of `stein-derived-groups-need-computable-modules-proof`), so `G_α' ↪ D_{m,N}`.
     This proves item 2. ∎
