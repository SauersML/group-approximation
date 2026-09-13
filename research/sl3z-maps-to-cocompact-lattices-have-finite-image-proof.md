---
rg: 2
id: sl3z-maps-to-cocompact-lattices-have-finite-image-proof
kind: route
title: Superrigidity extends the homomorphism to SL3(R); a nontrivial extension is an automorphism carrying a non-uniform lattice into the cocompact one
target: sl3z-maps-to-cocompact-lattices-have-finite-image
requires:
  - margulis-superrigidity-nonuniform-sl-n-lattices
---

Put `G = SL_3(R)`. `Γ'` is a lattice in `G` and `G/Γ'` is not compact, because `G/SL_3(Z)` is not compact and
`Γ'` has finite index.

1. **Extension.** Apply `margulis-superrigidity-nonuniform-sl-n-lattices` to `ϕ : Γ' → Λ ⊆ GL_3(R)`. This gives a
   continuous `ϕ̂ : G → GL_3(R)` and a finite-index `Γ'' <= Γ'` with `ϕ̂ = ρ` on `Γ''`.
2. **Dichotomy.** `ker ϕ̂` is a closed normal subgroup of `G`. As an abstract group `G` is simple, with trivial
   centre, so `ker ϕ̂` is `G` or `{1}`.
   * If `ker ϕ̂ = G`, then `ρ` is trivial on `Γ''`, and `|ρ(Γ')| <= [Γ' : Γ'']`. Done.
   * Otherwise `ϕ̂` is injective. `det∘ϕ̂` is a continuous homomorphism from the perfect group `G` to
     `R^×`, hence trivial, so `ϕ̂(G) ⊆ G`. The derivative `dϕ̂ : sl_3(R) → sl_3(R)` is an injective Lie
     algebra map, hence onto. So `ϕ̂(G)` is an open subgroup of the connected group `G`, which is `G`.
     Thus `ϕ̂` is a continuous bijective homomorphism `G → G`, a homeomorphism by the open mapping
     theorem for Lie groups.
3. **Contradiction.** `ϕ̂` preserves Haar measure up to a constant, so `ϕ̂(Γ'')` is a lattice in `G`. It lies
   in `Λ`, so it has finite index there, and `G/ϕ̂(Γ'')` is a finite cover of the compact space `G/Λ`,
   hence compact. But `gΓ'' ↦ ϕ̂(g)ϕ̂(Γ'')` is a homeomorphism `G/Γ'' → G/ϕ̂(Γ'')`, and `G/Γ''` is not
   compact. Contradiction. So only the first case occurs. ∎
