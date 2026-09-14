---
rg: 2
id: el-small-ball-generating-sets-from-grigorchuk-levels-proof
kind: route
title: Commuting supports, a four-factor normal form, and counting along inverted orbits
target: el-small-ball-generating-sets-from-grigorchuk-levels
requires: [sauer-schesler-grigorchuk-level-estimates]
artifacts:
  - research/artifacts/sk-free-8-nonuniform-growth-2026-09-13-part1.md
---

Full derivation: artifact part 1, §§2–3 (Lemmas 1–3, Theorem B). The artifact has `m = 3`; for general `m` replace `Sym(3)` by `Sym(m)` and `6` by `m!`.

1. **Generation.**
   - Permutation matrices lie in `EL(F_2)`, since `[[0,1],[1,0]] = e_12(1)e_21(1)e_12(1)` in characteristic 2.
   - Transitivity of `𝒢_n` spreads the fibre symmetric groups to every fibre. The linking transpositions give the edges of the connected graph `K_(2^(n−1),2^(n−1))` on sheet 1. So `⟨T_n⟩ ⊇ Sym(Y_n)`.
   - Conjugating the type-4 transvections gives every `e_(yy′)(σ)`. Sums and the commutator formula `[e_(ik)(r), e_(kj)(s)] = e_(ij)(rs)` then give every `e_(ij)(r)` with `r ∈ A`.
2. **Commuting supports** (for `n ≥ 5` and suffixes of length `≤ r_n/3`).
   - The type-2 conjugates live over `η_n h`, the type-3 conjugates over `ρ_n g, θ_n g`, and the type-4 conjugates over `ρ_n g`.
   - Coincidence of these points would force `d(ρ_n,η_n) ≤ 1 + 2r_n/3 < 2^(n−3)`, contradicting separation.
   - Type 3 (sheet 1) and type 4 (sheets 2 and 3) are disjoint. Type-4 conjugates commute pairwise, because `e_(yy′)(r)e_(yy′)(s) = e_(yy′)(r+s)` and different base points have disjoint supports.
3. **Normal form.** Pushing the type-1 letters to the left writes the element as `p_1p_2p_3p_4`, with `p_1 ∈ 𝒢_n` and `p_j` a product of conjugated factors of type `j` along the suffixes.
4. **Counting.**
   - `|P_1| ≤ exp(C ℓ^γ)`.
   - `|P_2| ≤ exp(C ℓ^α)·(m!)^(Cℓ^α)`.
   - `|P_3| ≤ exp(C(3ℓ)^α)·(C(3ℓ)^α)!`, using the word `ũ = (a_n g_1 a_n)⋯(a_n g_ℓ)`, whose suffixes realize both `ρ_n` and `θ_n` suffix points.
   - `|P_4| ≤ exp(C ℓ^α)·2^((|Σ|+1)Cℓ^α)`, since at each base point the factor is `e_((x,2),(x,3))(r_x)` with `r_x` in the `F_2`-span of `Σ ∪ {1}`.
   - The product is `≤ exp(C ℓ^β)` for any `β ∈ (max{α,γ},1)`.
