---
rg: 2
id: wreath-products-keep-the-abelianization-of-the-base
kind: claim
title: A permutational wreath product never puts a non-perfect base group into its derived subgroup
invalidates: [double-swap-embeds-group-in-derived-subgroup-proof]
distinct_from:
  rf-groups-lie-in-derived-subgroups-of-rf-groups: that builds an overgroup for residually finite groups through Ore's theorem in finite permutation groups; this says the cheap wreath-product substitute for that step cannot work for any group.
  whitehead-diagonal-map-is-not-multiplicative: that is the failure of `diag(a, a^{-1}, 1)` on noncommuting units; this is the group-theoretic obstruction behind the analogous wreath-product map.
  double-swap-embeds-group-in-derived-subgroup: that asserts the swap double works for every group; this contradicts it for every non-perfect base, since the swap double is the wreath product with two coordinates.
artifacts:
  - research/artifacts/sk-sofic-embedding-a-rank-route-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Λ` act transitively on a nonempty set `Ω`, let `Γ` be a group, and let
`Δ = Γ ≀_Ω Λ = (⊕_Ω Γ) ⋊ Λ`. Then `Δ^(ab) ≅ Γ^(ab) × Λ^(ab)`, and for the copy `Γ_ω ≤ Δ` at a coordinate `ω ∈ Ω`,

    Γ_ω ∩ [Δ, Δ] = [Γ, Γ]_ω .

So `Γ_ω ⊆ [Δ, Δ]` holds if and only if `Γ` is perfect.

Moreover, for `ω ≠ ω'` the map `γ ↦ γ_ω (γ^(-1))_(ω')`, whose values are the commutators `[γ_ω, λ]` when `λ` carries `ω`
to `ω'`, is a homomorphism if and only if `Γ` is abelian.

**Contradiction with a claim on main.** The swap double `Δ = (Γ × Γ) ⋊ C_2` of
`double-swap-embeds-group-in-derived-subgroup` is `Γ ≀ C_2`, the case `Ω = {1,2}`, `Λ = C_2`. That claim states that
`ι(γ) = (γ, γ^(-1)) = [(γ,1), s]` is an injective homomorphism onto a subgroup of `[Δ,Δ]`. The displayed computation
above shows `ι` is not multiplicative unless `Γ` is abelian, and reading the second factor as `Γ^(op)` does not repair
it: with any order-two automorphism exchanging the two factors, `[(γ,1), s]` is `(γ, γ)` in `Γ × Γ^(op)`, and the
homomorphism `γ ↦ (γ, γ^(-1))` of `Γ × Γ^(op)` is then not the commutator. The two requirements are compatible only for
abelian `Γ`.

**Why it matters.** Putting a group inside the derived subgroup of an overgroup is the step that makes
`γ ↦ diag(u_γ, 1, 1)` land in the elementary group
(`perfect-groups-embed-in-crossed-product-elementary-groups`). Wreath products are the cheapest candidate overgroups and
they preserve amenability, soficity and local embeddability, but this claim rules them out for every non-perfect group.
The known substitutes use finite permutation groups and Ore's theorem, so they need residual finiteness.

Route: `wreath-products-keep-the-abelianization-of-the-base-proof`.

**Review (sk-verify-4, 2026-09-13): PASS.** Coinvariants of a transitive action give `Δ^ab = Γ^ab × Λ^ab`, so `Γ_ω ∩ [Δ,Δ] = [Γ,Γ]_ω`; the order reversal in the second coordinate re-derived. Wired as invalidator of `double-swap-embeds-group-in-derived-subgroup-proof`. See `research/artifacts/sk-review-4-2026-09-13-part4.md` §1.
