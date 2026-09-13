---
rg: 2
id: tree-product-lattice-mixing-transfer-proof
kind: route
title: Couple the two lattices through L x B, move nonsoficity by stable orbit equivalence, and get mixing from factorwise ergodicity
target: tree-product-lattice-nonsofic-gives-mixing-nonsofic-action
requires:
  - product-of-tree-groups-has-factorwise-howe-moore
  - sofic-free-actions-are-soe-invariant
artifacts:
  - research/artifacts/product-tree-mixing-transfer-2026-09-12.md
---

# Proof

Full text: artifact Section 2.

1. **Coupling.** On `Ω = L × B` let `Λ` act by left multiplication on `L` and `Γ` by
   `(l, b) ↦ (lγ, γ^(-1)b)`. The actions commute, preserve `Haar ⊗ fair`, are free, and
   have finite-measure fundamental domains. The quotients are `Λ ↷ Ω/Γ = W` and
   `Γ ↷ Λ\Ω = (Λ\L) × B`.
2. **Freeness.** `Γ ↷ (Λ\L) × B` is free because `Γ ↷ B` is. If `λ[l,b] = [l,b]`, then
   `λl = lγ` and `γ^(-1)b = b` for some `γ`, so `γ = e` off a null set and `λ = e`.
3. **Nonsoficity.** `Γ` is not sofic, so none of its p.m.p. actions is sofic. The two
   quotient orbit relations are restrictions of the orbit relation of `Λ × Γ` on `Ω` to
   fundamental domains meeting every class. `sofic-free-actions-are-soe-invariant` makes
   `Λ ↷ W` nonsofic.
4. **Each factor is ergodic.** A `G_1`-invariant `F ∈ L^∞(W)` is a function on
   `G_1\L × B = G_2 × B` invariant under `(x, b) ↦ (x p_2(γ), γ^(-1)b)`. Its mean
   `F_0(x) = ∫ F(x,b) db` is invariant under the dense subgroup `p_2(Γ)` of right
   translations, hence constant. The rest `φ(x) = F(x,·) − F_0(x) ∈ L^2_0(B)` is bounded,
   measurable, and `φ(x p_2(γ)) = κ(γ)^(-1) φ(x)` for the Koopman representation `κ` of
   `B`, which is mixing. Density and non-discreteness of `G_2` give distinct `γ_n` with
   `p_2(γ_n) → e`, so `γ_n → ∞`. Continuity of translation in `L^1_loc(G_2; L^2_0(B))`
   gives, along a subsequence, `φ(x p_2(γ_n)) → φ(x)` in norm for almost every `x`, while
   `κ(γ_n)^(-1) φ(x) → 0` weakly. So `φ = 0` and `F` is constant. Same for `G_2`.
5. **Mixing.** `L^2_0(W)` has no nonzero `G_1`- or `G_2`-invariant vector, so
   `product-of-tree-groups-has-factorwise-howe-moore` makes `L ↷ W` mixing, and its
   restriction to the discrete subgroup `Λ` is mixing.

**Instance.** `K_p` consists of words with an even number of each involution of
`C_2^(*p)`, so of even length, so it preserves vertex types; it is discrete with finitely
many vertex orbits, hence a lattice of `Aut(T_p)^+`. `K_p × K_q` is a lattice of `L^+`,
a product of free groups, residually finite.
