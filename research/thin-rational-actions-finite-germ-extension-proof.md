---
rg: 2
id: thin-rational-actions-finite-germ-extension-proof
kind: route
title: Proof that thinness and clopen transitivity give the three Belk--Hyde--Matucci axioms for a finite germ extension
target: thin-rational-actions-give-finite-germ-extensions
requires:
  - rational-germ-singular-sets-are-finite-graph-path-spaces
  - germ-complex-and-bux-gonzalez-morse-inputs
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

Notation as in the claim.

## 1. Composition bounds, and axiom (1)

**Lemma.** For `g, h ∈ Homeo(∂L)`, `sing_B(gh) ⊆ sing_B(h) ∪ h^{-1}(sing_B(g))`, and
`sing_B(g^{-1}) = g(sing_B(g))`.

*Proof.* If `ξ ∉ sing_B(h)` and `h(ξ) ∉ sing_B(g)`, pick `b, b' ∈ B` with `h = b` near `ξ` and
`g = b'` near `h(ξ)`. Then `gh = b'b` near `ξ`, and `b'b ∈ B`. For the second statement, `g`
agrees with `b ∈ B` near `ξ` if and only if `g^{-1}` agrees with `b^{-1} ∈ B` near `g(ξ)`. ∎

Every element of `Γ` is a word in `S^{±1} ∪ B`, and elements of `B` have empty singular set, so
by induction on word length its singular set is contained in a finite union of translates of
the sets `sing_B(s)`, `s ∈ S`. By (T) each of those is finite, so every element of `Γ` has
finitely many singular points. That is axiom (1). The same computation gives
`sing(Γ) ⊆ G·(⋃_s sing_B(s))`, and the reverse inclusion is immediate, which with item 3 of
`rational-germ-singular-sets-are-finite-graph-path-spaces` gives item 2 of the claim:
`sing(Γ)` is a countable set of eventually periodic points. ∎

## 2. Axiom (2)

`B ≤ Γ` by definition of `Γ`. Conversely let `h ∈ Γ` with `sing_B(h) = ∅`. Then every point of
`∂L` has a neighbourhood on which `h` agrees with an element of `B`, hence a neighbourhood on
which `h` is a prefix replacement. That is the definition of `B`, so `h ∈ B`. ∎

## 3. Axiom (3), from clopen transitivity

Let `g ∈ Γ` and `p ∈ sing_B(g)`. By axiom (1) the set `sing_B(g)` is finite, so we may choose a
cylinder `[u] ∋ p` of `∂L` with `[u] ∩ sing_B(g) = {p}` and `[u] ≠ ∂L`; shrinking further we
may also assume `g([u]) ≠ ∂L`, since `g([u])` is a cylinder-like clopen set whose diameter
shrinks with `[u]` and `∂L` is perfect and hence infinite.

Both `∂L ∖ [u]` and `∂L ∖ g([u])` are nonempty clopen sets, so by (E5) there is a `B`-local
bijection `β : ∂L ∖ [u] → ∂L ∖ g([u])`. Define

    h = g on [u],    h = β on ∂L ∖ [u].

Then `h` is a homeomorphism of `∂L`: it is a bijection because `g([u])` and `∂L ∖ g([u])`
partition `∂L`, and it is continuous with continuous inverse because `[u]` is clopen.

`h` agrees with `g` on the neighbourhood `[u]` of `p`, in particular near `p`.

`sing_B(h) = {p}`: on `∂L ∖ [u]` the map `h = β` is locally a prefix replacement, so no point
there is singular; on `[u] ∖ {p}` we have `h = g` and those points are not in `sing_B(g)`, and
singularity is a local condition, so they are not in `sing_B(h)`; and `p ∈ sing_B(h)` because
`h = g` near `p` and `p ∈ sing_B(g)`.

Finally `h ∈ Γ`: the map `h g^{-1}` is the identity on `g([u])` and equals `β g^{-1}` on
`∂L ∖ g([u])`, where `g` is locally a prefix replacement (no singular points of `g` lie in
`∂L ∖ [u]`); so `h g^{-1}` is locally a prefix replacement everywhere, hence lies in `B` by
step 2, and `h = (h g^{-1}) g ∈ ⟨B, g⟩ ≤ Γ`. ∎

This is axiom (3), and with steps 1 and 2 it proves item 1 of the claim. Item 3 of the claim is
the bookkeeping remark that (E1) of `automatic-groups-embed-in-corner-germ-extensions` is
exactly axioms (1)-(3) for `Γ` over `B`.

## 4. Trust surface

- The axioms for a finite germ extension are Belk--Hyde--Matucci §1, quoted in
  `germ-complex-and-bux-gonzalez-morse-inputs`.
- Thinness and eventual periodicity are imported from
  `rational-germ-singular-sets-are-finite-graph-path-spaces`.
- Nothing else is cited; steps 1-3 are elementary.
