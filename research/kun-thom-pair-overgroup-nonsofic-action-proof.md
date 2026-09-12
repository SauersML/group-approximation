---
rg: 2
id: kun-thom-pair-overgroup-nonsofic-action-proof
kind: route
title: Co-induce the Kun--Thom free nonsofic action to the overgroup and multiply by its Bernoulli shift
target: groups-containing-kun-thom-pair-have-nonsofic-actions
requires:
  - kun-thom-free-nonsofic-action
  - sofic-action-class-closed-under-commensurability
---

# Proof

Let `Γ <= G <= L` be as in the claim and `Z` the free ergodic nonsofic
`G`-action supplied by `kun-thom-free-nonsofic-action`.

1. `CoInd_G^L(Z)` is not sofic. By Lemma B of
   `sofic-action-class-commensurability-proof`, `Z` is a `G`-factor of the
   restriction of `CoInd_G^L(Z)` to `G`. By Lemma A there, a sofic
   `L`-action would make that factor sofic, contradicting the choice of `Z`.
2. `G` is infinite (it contains the infinite-index subgroup `Γ`), so `L` is
   infinite and its Bernoulli shift `B_L = ({0,1},fair)^L` is essentially free.
   The diagonal action on `X_L = CoInd_G^L(Z) × B_L` is essentially free:
   the fixed-point set of `g ≠ 1` lies in `CoInd_G^L(Z) × Fix_(B_L)(g)`, a null set.
3. `CoInd_G^L(Z)` is an `L`-factor of `X_L`, so by Lemma A with `K = L`,
   soficity of `X_L` would make `CoInd_G^L(Z)` sofic, contradicting step 1.

So `X_L` is an essentially free nonsofic p.m.p. action of `L`, and `L ∉ 𝒮`.
