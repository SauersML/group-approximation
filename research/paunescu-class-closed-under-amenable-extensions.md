---
rg: 2
id: paunescu-class-closed-under-amenable-extensions
kind: claim
title: An action whose restriction to a normal subgroup with amenable quotient is sofic is sofic, so Paunescu's class is closed under amenable extensions
distinct_from:
  sofic-kernel-amenable-quotient-permanence: that is the group-level statement, sofic kernel and amenable quotient give a sofic group; this is the action-level statement, for every p.m.p. action and Paunescu's crossed-product soficity
  sofic-action-class-closed-under-commensurability: that covers finite-index overgroups by monomial induction; this covers every extension with amenable quotient by Folner induction, of which the finite-index case is the special case of a finite quotient
  paunescu-sofic-action-class-permanence: that imports Paunescu's permanence (amenable groups, free groups, amalgams over amenable subgroups); this adds extensions with amenable quotient
artifacts:
  - research/artifacts/paunescu-class-amenable-extensions-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `N ◁ G` be countable groups with `G/N` amenable, and
`G ↷ (X, μ)` a p.m.p. action. If `N ↷ X` is sofic (Păunescu Definition 1.4), then `G ↷ X` is
sofic. Consequently, if every action of `N` is sofic, so is every action of `G`: Păunescu's
class `𝒮` is closed under extensions with amenable quotient.

**Instances.** `N ⋊ Z^d`, `N × A` with `A` amenable, free-by-cyclic groups `F_n ⋊ Z`,
surface-by-cyclic groups, and the fundamental groups of closed hyperbolic 3-manifolds
(`hyperbolic-3-manifold-groups-in-paunescu-class`).

**Mechanism.** Induce over a Følner window `F ⊆ G/N`: with a section `s` and the cocycle
`h(g, q) = s(gq)^{-1} g s(q) ∈ N`, send `f` to `Σ_q e_(q,q) ⊗ α_(s(q)^{-1})(f)` and `u_g` to
`Σ_q e_(gq,q) ⊗ u_(h(g,q))` in `M_F ⊗ (L^∞(X) ⋊ N)`. Covariance and the trace are exact, the group
law fails only on `F ∖ g^{-1}F`, and a sofic embedding of the `N`-action turns the blocks into
permutations.

**For the roots.** Nonsoficity of actions is not created by amenable extensions: if `G ∉ 𝒮` and
`G/N` is amenable, then `N ∉ 𝒮`. And no infinite Kazhdan group enters `𝒮` this way, since amenable
quotients of Kazhdan groups are finite.

Proof in `paunescu-class-amenable-extension-proof`.
