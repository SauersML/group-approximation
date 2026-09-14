---
rg: 2
id: perfect-groups-embed-in-crossed-product-elementary-groups-proof
kind: route
title: Whitehead's lemma on the canonical units, with the K_1 class as the obstruction
target: perfect-groups-embed-in-crossed-product-elementary-groups
requires: []
artifacts:
  - research/artifacts/sk-sofic-embedding-a-rank-route-2026-09-13.md
---

1. **The homomorphism.** Every element of `R = LC(X,k) ⋊ Δ` is a unique finite sum `Σ_γ f_γ u_γ`, and
   `u_γ u_δ = u_(γδ)`, so `u` is a homomorphism `Δ → R^×`, injective because `u_γ = 1` forces `γ = e` by uniqueness of
   the coefficients. Composing with the homomorphism `a ↦ diag(a,1,1)` of `R^×` into `GL_3(R)` gives 1.
2. **The obstruction.** `K_1(R) = GL(R)/E(R)` is abelian, and `[diag(a,1,1)] = [a]` for `a ∈ R^×`. So
   `γ ↦ [u_γ]` is a homomorphism into an abelian group; `diag(u_γ,1,1) ∈ E(R)` exactly when this class vanishes, and the
   kernel of a homomorphism is normal. This proves 2.
3. **Commutators are elementary.** Whitehead's lemma gives `diag(a,a^(-1),1) ∈ E_3(R)` for every `a ∈ R^×`: the matrix
   is a product of six elementary matrices,

       diag(a,a^(-1),1) = e_12(a) e_21(-a^(-1)) e_12(a) · e_12(-1) e_21(1) e_12(-1) ,

   the standard identity in `GL_2` embedded in the upper left corner. Multiplying the three Whitehead matrices displayed
   in the claim and cancelling gives `diag(αβα^(-1)β^(-1),1,1)` with `α = u_a`, `β = u_b`; writing it out,
   `diag(a,a^(-1),1)·diag(b,b^(-1),1) = diag(ab, a^(-1)b^(-1),1)` and multiplying by
   `diag((ba)^(-1), ba, 1)` gives `diag(ab(ba)^(-1), a^(-1)b^(-1)ba, 1) = diag([a,b],1,1)` with
   `[a,b] = aba^(-1)b^(-1)`. Each factor lies in `E_3(R) = EL_3(R)`, so the product does. Applying this with
   `a = u_α`, `b = u_β` and `u_[α,β] = [u_α, u_β]` proves 3, and a product of commutators maps to a product of
   elementary matrices.
4. **Perfect case.** If `Δ = [Δ,Δ]` then every `u_γ` is a product of commutators of units, so the image of `Δ` lies in
   `EL_3(R)`, and the map is injective by 1.

**Model tests.**
- `Δ` abelian and nontrivial: step 3 gives nothing, and for `Δ = Z` over a minimal subshift the image really is outside
  the elementary group, so the criterion is not vacuous.
- `Δ` simple and nonabelian, for instance a derived topological full group: perfect, so the whole group embeds.
- `X` a point and `Δ` perfect: `R = k[Δ]`, and the statement reduces to the classical fact that the image of a perfect
  group in `K_1(k[Δ])` is trivial.
