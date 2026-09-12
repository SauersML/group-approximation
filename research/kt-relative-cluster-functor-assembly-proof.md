---
rg: 2
id: kt-relative-cluster-functor-assembly-proof
kind: route
title: Transport, improve, and close every functor law with the distance gap
target: kt-relative-cluster-functor-assembly
requires: []
artifacts:
  - GroupApproximation/KunThom/RelativeFunctorMetric.lean
  - GroupApproximation/KunThom/RelativeFunctorAssembly.lean
---

## Direct proof, machine-checked

- **Representatives.** `transportRep` chooses, for a representative `b`, an
  improvement of `sandwich (bridge X) (bridge Y) b` within `ρ X Y`.
  `relativeMorphism` is the morphism of the restricted presentations. The functor is
  `GroupoidPresentation.Morphism.toFunctor`.
- **Four triangle chains.** Each is a count built from the landed transport lemmas
  `twoSidedDisagreement_sandwich_le`, `_sandwich_refl`, `_sandwich_trans_le` and
  `_sandwich_roundtrip_le`, with the triangle inequality.
  - `twoSidedDisagreement_transport_le`: well-definedness. Related representatives
    have related improvements.
  - `twoSidedDisagreement_transport_refl_le`: the identity.
  - `twoSidedDisagreement_transport_comp_le`: composition, through the improved
    composite in the source and in the target.
  - `twoSidedDisagreement_transport_reflect_le`: faithfulness, by transporting
    back through the reversed bridges.
- **Closing with the gap.** Every chain ends below eight times the target radius
  of the pair, or of the source pair for faithfulness. The clause `rel_of_lt`,
  the distance gap of the cluster groupoid, turns that into relatedness.
- **Estimate (7).** The representative `θ` is related to the chosen improvement
  (`Quotient.exact`), so it is within the target radius of it, and the improvement
  is within `ρ` of the raw map.

Probe GREEN at base 9105379d6, tag 0912-133134-83196. All sixteen printed axiom
closures are `[propext, Classical.choice, Quot.sound]`.
