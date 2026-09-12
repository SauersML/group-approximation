---
rg: 2
id: sofic-action-class-closed-under-commensurability
kind: claim
title: Paunescu's class of groups with only sofic actions is closed under subgroups and finite-index overgroups
distinct_from:
  paunescu-sofic-action-class-permanence: that imports Paunescu's own permanence (amenable groups, free groups, amalgamation over amenable subgroups); this proves two further permanence properties, subgroups and finite-index overgroups, which that paper does not state
  gkp-sofic-action-toolkit: that is restriction permanence for sofic actions on countable sets; this concerns the class of groups all of whose p.m.p. actions are sofic, where passing to a subgroup needs co-induction rather than restriction
---

**ESTABLISHED.** Let `𝒮` be Păunescu's class of countable groups all of whose
p.m.p. actions are sofic (Definition 3.2, soficity as in Definition 1.4; see
`paunescu-sofic-action-class-permanence`).

1. **Subgroups.** If `G ∈ 𝒮` and `H <= G`, then `H ∈ 𝒮`. More precisely every
   p.m.p. action `H ↷ Z` is an `H`-factor of the restriction to `H` of the
   co-induced action `CoInd_H^G(Z)`, and a factor of a restriction of a sofic
   action is sofic.
2. **Finite-index overgroups.** If `H <= G` has finite index and `H ∈ 𝒮`, then
   `G ∈ 𝒮`. For every p.m.p. action `G ↷ X` the crossed product
   `L^∞(X) ⋊ G` embeds trace-preservingly in `M_n(L^∞(X) ⋊ H)`, `n = [G:H]`, by
   a monomial induction matrix that keeps the base diagonal and sends each `u_g`
   to a block permutation of `H`-unitaries.
3. **Consequence.** Membership in `𝒮` depends only on the commensurability
   class of the group, and a group with one nonsofic p.m.p. action passes that
   property to every overgroup. With Păunescu's Theorem 3.1 the transferred
   action can be taken free: multiply by a Bernoulli shift.

The proofs are in `sofic-action-class-commensurability-proof`.

**Why it is worth a node.** `kun-thom-free-nonsofic-action` puts one specific
residually finite group outside `𝒮`. Part 1 turns that into a statement about
every group containing it (`groups-containing-kun-thom-pair-have-nonsofic-actions`),
and part 2 shows the property cannot be removed by passing to a finite-index
subgroup or overgroup.
