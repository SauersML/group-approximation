---
rg: 2
id: artin-complex-top-homology-is-intersection-of-ideals-proof
kind: route
title: "Proof: top simplices are group elements, codimension-one faces are cosets of the cyclic subgroups, and cycles are balanced along those cosets"
target: artin-complex-top-homology-is-intersection-of-ideals
requires: []
---

**Literature inputs.** Standard parabolic subgroups are the Artin groups of the induced
subgraphs (van der Lek; L. Paris, arXiv:1211.7339, Theorem 5.4), and
`A_X ∩ A_Y = A_{X ∩ Y}` for `X, Y ⊆ S` (H. van der Lek, thesis, Nijmegen 1983; this
intersection statement is attributed to van der Lek throughout the literature, but its
theorem number was not checked in this pass). In particular `A_{\{s\}} = ⟨s⟩ ≅ Z`.

**1. Simplices.** Two distinct cosets of the same `P_s` are disjoint, so a simplex has at
most one vertex of each type `s`. If cosets `g_s P_s` (`s ∈ R`, `∅ ≠ R ⊆ S`) have a
common element `g`, then `g_s P_s = gP_s`, and their intersection is
`g ⋂_{s∈R} A_{S∖{s}} = g A_{S∖R}`. For `R = S` this is `{g}`, so the `(n − 1)`-simplices are
the `σ_g = {gP_s : s ∈ S}`, `σ_g` determines `g` as its unique common element, and
`hσ_g = σ_{hg}`. For `R = S ∖ {s}` the intersection is `g⟨s⟩`, so the face of `σ_g` missing
type `s` is `τ_{s, g⟨s⟩} = {gP_t : t ≠ s}`, and it depends exactly on the coset `g⟨s⟩`.

**2. Top homology.** Fix a total order on `S` and orient every simplex by the order of its
vertex types. Left translation preserves types, so the simplicial chain complex
`C_*(Δ(A))` is a complex of left `ZA`-modules, and `C_{n−1} ≅ ZA` via `σ_g ↦ g`. The
boundary is `∂σ_g = Σ_{s ∈ S} ε_s τ_{s, g⟨s⟩}` with signs `ε_s = ±1` depending only on
`s`. Faces of different types are different simplices, so for `x = Σ_g a_g g`,

`∂(Σ_g a_g σ_g) = Σ_s ε_s Σ_{c ∈ A/⟨s⟩} (Σ_{g ∈ c} a_g) τ_{s,c}`,

which vanishes iff `Σ_{g ∈ c} a_g = 0` for every `s` and every coset `c = g⟨s⟩`, i.e. iff
`x` lies in the kernel of every map `π_s : ZA → Z[A/⟨s⟩]`, `g ↦ g⟨s⟩`. There are no
`n`-simplices, so `H_{n−1}(Δ(A)) = ker ∂_{n−1} ≅ ⋂_s ker π_s`. For a subgroup `H ≤ G` the
kernel of `ZG → Z[G/H]` is spanned by the elements `g − gh = g(1 − h)`, so it is
`ZG·I_H`, where `I_H` is the augmentation ideal of `ZH`. For `H = ⟨s⟩` infinite cyclic,
`I_H = ZH·(1 − s)`, since `1 − s^k = (1 + s + ⋯ + s^{k−1})(1 − s)` and
`1 − s^{−k} = −s^{−k}(1 − s^k)`. So `ker π_s = ZA·(1 − s)`, and item 2 follows.

**3. Finite `W`.** Let `θ : A → W` be the canonical quotient. By Matsumoto's theorem (the
reduced expressions of an element of `W` are connected by braid moves; Tits,
*Le problème des mots dans les groupes de Coxeter*, 1969), the positive lift
`σ(w) = s_1 ⋯ s_k` of a reduced expression `w = s_1 ⋯ s_k` is well defined, and
`θ(σ(w)) = w`, so `σ` is injective. Fix `s ∈ S`. `W` is the disjoint union of the pairs
`{w, ws}` with `ℓ(ws) = ℓ(w) + 1`, and for such `w` a reduced expression of `w` followed
by `s` is reduced, so `σ(ws) = σ(w)s`. Hence

`x_W = Σ_{w : ℓ(ws) > ℓ(w)} (−1)^{ℓ(w)} σ(w)(1 − s) ∈ ZA·(1 − s)`.

This holds for every `s`, and `x_W ≠ 0` because the `σ(w)` are distinct and every
coefficient is `±1`. ∎
