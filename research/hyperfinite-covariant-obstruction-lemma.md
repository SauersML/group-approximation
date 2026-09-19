---
rg: 2
id: hyperfinite-covariant-obstruction-lemma
kind: claim
title: A properly outer action of a nonamenable group on the lamp closure has no finite injective covariant representation
distinct_from:
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that obstructs Kazhdan groups inside U(R) through Kirchberg's finite-dimensional approximation; this obstructs semidirect products Λ ⋊ Σ through outerness of the Σ-action on the lamp von Neumann algebra and nonamenability of Σ, and needs no property (T).
  literal-canonical-shift-model-stops-at-r-omega: that applies the conditional-expectation argument to the canonical crossed product, where the regular character on V is given; this lemma derives the regular character from proper outerness of the action on the lamp closure, for an arbitrary covariant representation.
  hyperfinite-factor-qd-forces-unitary-subgroups-mf: that is the reduction of X(2) to unitary subgroups of R; this is a tool for showing that specific groups are not unitary subgroups of R.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `Γ = Λ ⋊ Σ` be a semidirect product of countable groups and let
`ρ : Γ → U(W)` be a homomorphism into the unitary group of a finite von
Neumann algebra `W` with faithful normal tracial state `τ_W`.  Put
`M = ρ(Λ)'' ⊆ W` and `α_g = Ad ρ(g)|_M` for `g ∈ Σ`.  Suppose that for every
`g ∈ Σ \ {e}` the automorphism `α_g` is properly outer on `M`: there is no
nonzero `x ∈ M` with `x a = α_g(a) x` for all `a ∈ M`.

Then `τ_W(ρ(g)) = 0` for every `g ∈ Σ \ {e}`, the von Neumann algebra
`ρ(Σ)'' ⊆ W` is isomorphic to the group von Neumann algebra `L(Σ)`, and if
`W` is injective then `Σ` is amenable.

Equivalently: if `Σ` is not amenable, then no representation of `Λ ⋊ Σ`
into a finite injective von Neumann algebra makes the `Σ`-action on the
lamp closure properly outer.  When `M` is a factor, proper outerness is
just outerness.
