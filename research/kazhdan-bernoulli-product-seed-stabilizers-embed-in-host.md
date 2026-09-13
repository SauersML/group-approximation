---
rg: 2
id: kazhdan-bernoulli-product-seed-stabilizers-embed-in-host
kind: claim
title: If the relation of a Bernoulli shift times an arbitrary action of a Kazhdan group sits inside a free action's orbit relation, almost every stabilizer of the arbitrary factor maps into the host with finite kernel
distinct_from:
  rigid-bernoulli-seed-relations-embed-their-group-in-the-host: that treats factors of Bernoulli shifts and gives one finite-kernel morphism of the whole seed group; this treats products Bernoulli × τ with τ arbitrary, where Popa's theorem untwists only to a cocycle of τ, and gives finite-kernel morphisms of the stabilizers of τ
  simple-kazhdan-bernoulli-relation-hosts-contain-the-group: that is the Bernoulli seed of a simple Kazhdan group; this is the product case, and it recovers a finite-kernel form of that statement when τ is trivial
---

**ESTABLISHED (unreviewed).** Let `H` be an infinite countable group with property (T), and `(Y_0,ν_0)` a nontrivial
standard probability space. Let `σ` be the Bernoulli shift `H ↷ (Z,ζ) := (Y_0,ν_0)^H`, and `τ : H ↷ (W,ω)` an
arbitrary p.m.p. action by Borel automorphisms of a standard probability space. Let `H` act diagonally on
`Z × W`. The action is essentially free because `σ` is.

Let `G' ↷ (X,μ)` be an essentially free p.m.p. action of a countable group, and `A ⊆ X` measurable with
`μ(A) > 0`. Let `θ : (Z × W, ζ × ω) → (A,μ_A)` be a measure-space isomorphism with `θ(h·ξ) ∈ G'·θ(ξ)` for every
`h ∈ H` and a.e. `ξ`. Then for `ω`-a.e. `w`, the stabilizer `S_w := {h ∈ H : h·w = w}` admits a morphism
`ρ_w : S_w → G'` with finite kernel.

## Consequences

1. **Trivial `τ`.** `S_w = H`, so there is a finite-kernel morphism `H → G'`. This is the Kazhdan case of
   `rigid-bernoulli-seed-relations-embed-their-group-in-the-host`.
2. **Sofic hosts see only small stabilizers.** If `G'` is sofic, then for a.e. `w` some quotient of `S_w` by a finite
   normal subgroup is sofic (`sofic-passes-to-subgroups`). So the invariant random subgroup `w ↦ S_w` of `τ` must be
   concentrated on such subgroups. The same holds with "sofic" replaced by "residually finite" or "linear" for hosts
   of those kinds.
3. **What survives.** If `τ` is essentially free, all stabilizers are trivial and the theorem says nothing. So among
   product seeds `Bernoulli × τ` of Kazhdan groups, the open case is `τ` essentially free (or with stabilizers that
   embed into the host modulo finite subgroups) and not a factor of a Bernoulli shift.

## Scope

The seed group is assumed Kazhdan, so the rigid subgroup is the whole group. Groups with only a wq-normal Kazhdan
subgroup, such as the Kun--Thom wreaths, would need the spreading step of
`rigid-bernoulli-seed-host-via-popa-and-wq-normal-extension`. That step is not adapted here, because in the product
case the untwisted cocycle depends on `w`.

**Trust surface.** The product clause of Popa's Theorem 0.1 and his weak-mixing criterion, both quoted verbatim on
main. No novelty is claimed.

Proof: `kazhdan-bernoulli-product-seed-stabilizer-proof`.
