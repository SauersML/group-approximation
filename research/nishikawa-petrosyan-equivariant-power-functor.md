---
rg: 2
id: nishikawa-petrosyan-equivariant-power-functor
kind: claim
title: Tensor powers define a unique functor KK_G → KK_(G wr_Ω F), and gamma elements of G power to gamma elements of G wr_Ω F
distinct_from:
  kk-tensor-power-norm-functor-to-kk-zp: that is the repo's norm functor KK → KK^(Z/p), items 1-3 of which are the case G = 1, F = Ω = Z/p of this imported theorem; this is the literature statement itself, with equivariance over G and the gamma-element compatibility.
---

**ESTABLISHED (citation).** Let `G` and `F` be second countable locally compact groups, `Ω` a finite
`F`-set, and `G ≀_Ω F = (∏_Ω G) ⋊ F`.

1. **The power functor.** For separable `G`-C\*-algebras `A` and `B` there is a map
   `⊗̂_Ω : KK_G(A, B) → KK_(G≀_Ω F)(A^(⊗Ω), B^(⊗Ω))` with these properties.
   - It sends the class of a `G`-\*-homomorphism `φ` to the class of `φ^(⊗Ω)`.
   - It is compatible with Kasparov products against \*-homomorphisms on either side.
   - It sends `KK_G`-equivalences to `KK_(G≀_Ω F)`-equivalences.
   - On ungraded algebras it is a functor, and the unique functor sending `[φ]` to `[φ^(⊗Ω)]`.
2. **Restrictions.** For every continuous homomorphism `L → G ≀_Ω F`, restricting to `L` gives the
   unique functor `KK_G → KK_L` sending `A` to `A^(⊗Ω)` and `[φ]` to `[φ^(⊗Ω)]`.
3. **Gamma elements.** If `G` has a gamma element `γ_G` in the Meyer–Nest sense, then for every
   compact `F` and finite `F`-set `Ω`, `G ≀_Ω F` has one, and `γ_(G≀_Ω F) = ⊗̂_Ω(γ_G)`. If `γ_G = 1`,
   then `γ_(G≀_Ω F) = 1`.
4. **The Izumi filtration.** For a c.p.-split extension `0 → I → A → A/I → 0` of `G`-algebras,
   `A^(⊗Ω)` has a filtration by `G ≀_Ω F`-invariant ideals `I_j`, the closed spans of
   `I^(⊗S) ⊗ A^(⊗Ω∖S)` over `|S| = j`. The subquotients are canonically
   `I_j/I_(j+1) ≅ ⊕_(|S| = j) I^(⊗S) ⊗ (A/I)^(⊗Ω∖S)`, and each step is c.p.-split.

Proof: `nishikawa-petrosyan-equivariant-power-functor-citation`.
