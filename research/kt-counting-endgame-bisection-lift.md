---
rg: 2
id: kt-counting-endgame-bisection-lift
kind: claim
title: Finite counting endgame of Kun--Thom Theorem 4.1 on cluster groupoids
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Theorem 4.1 itself, imported by citation; this is one finite combinatorial step of its proof, proved in Lean, and the theorem does not follow from it without the other steps.
  kt-relative-cluster-functor-assembly: that builds the relative cluster functor of Lemma 4.3 and proves it faithful; this consumes any faithful functor injective on objects and lifts a total bisection through it by counting orbits and isotropy groups.
artifacts:
  - GroupApproximation/KunThom/CountingEndgameCompletion.lean
  - GroupApproximation/KunThom/CountingEndgameLift.lean
  - GroupApproximation/KunThom/CountingEndgameWeights.lean
  - GroupApproximation/KunThom/CountingEndgameRestrict.lean
  - GroupApproximation/KunThom/CountingEndgameSelection.lean
---

**ESTABLISHED in Lean.** This is the finite step of the counting in Kun and
Thom's proof of Theorem 4.1 (arXiv:2608.06222v3, §4, tex lines 1110–1313),
stated for abstract finite groupoids.

The data:
- `F : C' ⥤ D` is faithful and injective on objects (the relative cluster
  functor of a compressor);
- `J : C' ⥤ C` is injective on objects (the inclusion of the restriction);
- `a` is a total bisection of `D`;
- `S` is a finite set of objects of `C'`, and `sel` chooses targets with
  `F (sel X) = a (F X)`.

Suppose that at every `X ∈ S`:
- the orbit of `F X` has fewer objects than the orbits of `X` and `sel X`
  together;
- the isotropy index of `F` at `X` is below `2`.

Then every transported arrow of `a` has a preimage `g : X ⟶ sel X`, and some
total bisection of `C` carries `J g` at every `J X`. This is
`CountingEndgame.exists_bisection_lift`. With `S` taken to be the objects where the
target condition and both counts hold (`CountingEndgame.selected`), it needs no
per-object hypothesis (`exists_bisection_lift_selected`).

Supporting finite facts, all in namespace `GroupApproximation.CountingEndgame`:
- `Ω₁ = Ω₂` (`nonempty_hom_of_card_orbit_lt_add`) and the Hom-set bijection
  (`map_bijective_of_counts`);
- completion of a partial bisection inside every connected component
  (`exists_bisection_extend`, `exists_bisection_extend_of_injOn`);
- the two count hypotheses from clean orbits and ratio bounds
  (`card_lt_add_of_ratio`, `lt_two_mul_of_ratio`);
- the weight of the completion (`sum_compl_image_le`), of preimages
  (`sum_filter_image_le`) and of non-clean orbits (`mul_sum_le_of_dirty`);
- the bridge to restricted presentations: the inclusion functor
  `GroupoidPresentation.restrictInclusionFunctor`, faithful, full and injective on
  objects, and with ambient orbits and isotropy groups the one-sided
  inequalities (2) and (3) (`mul_card_orbit_le_card_orbit_map_of_clean`,
  `card_vertexGroup_le_card_vertexGroup_map`) and the two count hypotheses
  (`card_orbit_lt_add_of_clean`, `card_vertexGroup_lt_two_mul_of_ratio`).

**What this does not give.** The asymptotic assembly of the counting is not
proved here. That is the choice of the cleanliness scale `ζ_n`, the conull set
`E_n`, and the Props `OneSided`, `Concentrated` and `Transported` of
`CompressorNormalizationAssembly.seqNormalizes_of_compressor_of_steps`. So this
node does not derive `kun-thom-sofic-centralizer-normalization`.

Derivation: `kt-counting-endgame-bisection-lift-proof`.
