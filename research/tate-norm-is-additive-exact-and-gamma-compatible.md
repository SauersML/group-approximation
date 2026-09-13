---
rg: 2
id: tate-norm-is-additive-exact-and-gamma-compatible
kind: claim
title: After tensoring with the Tate object, the equivariant power functor KK^Γ → KK^(Γ ≀ Z/p) is additive, exact on mapping cones, and carries the γ-decomposition to the γ-decomposition
distinct_from:
  kk-tensor-power-norm-functor-to-kk-zp: that is the non-additive norm functor KK → KK^(Z/p); this shows its Tate localization over Γ is additive and exact, which replaces the unproved norm sum formula.
  nishikawa-petrosyan-equivariant-power-functor: that imports the power functor and its Izumi filtration; this derives additivity, exactness and γ-compatibility after ⊗ q^*1_T.
---

**ESTABLISHED (derivation; unreviewed).**
- **Setting.** `p` is prime, `G = Z/p`, `Γ` is countable discrete, and `W = Γ ≀ G` with
  `q : W → G`.
- **The Tate norm.** `T(A) := q^*1_T ⊗ ⊗̂_G(A)` defines `T : KK^Γ → KK^W`, where `⊗̂_G` is the
  Nishikawa–Petrosyan power functor with `Ω = G`.

1. `T` is a functor, and `T([φ]) = 1 ⊗ [φ^(⊗p)]`.
2. `T` preserves finite biproducts, so `T(x + y) = T(x) + T(y)`. Non-constant tensor words form free
   `G`-orbits, which are induced from `Γ^p` and die against `q^*1_T`.
3. For a `Γ`-\*-homomorphism `φ : A → B` there is an exact triangle `T(C_φ) → T(A) → T(B)`, whose
   second arrow is `T(φ)`.
4. If `Γ` is torsion-free and has a γ-element, then `T(γA) = γ_W T(A)` and
   `T((1 − γ)A) = (1 − γ_W)T(A)`.
5. `T(Ind_K^Γ B) ≅ Ind_(K≀G)^W(Res q^*1_T ⊗ B^(⊗p))`.

**Dependency at odd `p`.**
- This claim uses the power functor only through Nishikawa–Petrosyan Theorems 5.10–5.11. Their
  Kasparov partition has pairwise compact commutators and exact `S_N`-symmetry.
- It never uses Proposition 1 of `research/artifacts/uct-kk-norm-functor-2026-09-13-part1.md`, whose
  odd-`p` compactness gap was found by ex-verify2-analysis at a272b661a2.
- So it holds for every prime `p`.
- The reformulation and split nodes `tate-diagonal-cone-is-weakly-contractible-wreath-object` and
  `kazhdan-tate-diagonal-from-crossed-product-and-no-phantom` use no norm functor at all, only the
  \*-homomorphism `1_T ⊗ Δ`.

**Consequence.**
- `T(1 − γ_Γ) = 1 − γ_W ⊗ 1`.
- The Tate diagonal question `kazhdan-group-algebra-tate-diagonal-is-kkg-equivalence` lives entirely
  on the Skandalis summand `T((1 − γ)C)`. Before this claim that reduction was conditional on the norm
  sum formula.

Proof: `tate-norm-is-additive-exact-and-gamma-compatible-proof`.
