---
rg: 2
id: thompson-t-is-isomorphic-to-ppsl2z
kind: claim
title: Thompson's group T is isomorphic, by conjugation with a circle homeomorphism, to the group PPSL_2(Z) of homeomorphisms of the projective line that are piecewise PSL_2(Z) with finitely many breakpoints, all rational (Thurston, Imbert)
distinct_from:
  psl2z-in-thompson-t-has-amenable-centralizers-in-v: that imports the same Haagerup--Olesen copy Λ of PSL(2,Z) for its centralizer bound (non-inner amenability); this imports only the isomorphism with the verbatim breakpoint convention of Definition 2.1, which the almost-malnormality proof uses.
  thompson-t-orbits-carry-no-invariant-means: that uses the dyadic piecewise-linear model of T; this imports the piecewise projective model, in which PSL_2(Z) is a subgroup.
---

**ESTABLISHED (literature import).** Let `PPSL_2(Z)` be the group of homeomorphisms of
`RP^1 = R ∪ {∞}` that are piecewise Möbius transformations from `PSL_2(Z)` and have finitely many
breakpoints, all in `Q ∪ {∞}`. Here a *breakpoint* of `g` is a point `x` with no open
neighbourhood `U` on which `g` agrees with a single element of `PSL_2(Z)`.

Then there is a homeomorphism `φ : RP^1 → R/Z` such that `g ↦ φ ∘ g ∘ φ^{-1}` is an isomorphism
`Φ : PPSL_2(Z) → T` (Thurston; Imbert's version). The Minkowski question mark function
`?` also works as `φ` (Fossas's statement of Imbert's theorem).

In particular `PSL_2(Z)` (the elements with no breakpoint) is a subgroup of `PPSL_2(Z)`, and
`Λ = Φ(PSL_2(Z)) ≅ Z/2 * Z/3` is a subgroup of `T`. This is the copy of `PSL_2(Z)` meant in
`thompson-t-co-amenable-subgroup-kills-real-euler-class`.

Route: `thompson-t-ppsl2z-imbert-citation`.
