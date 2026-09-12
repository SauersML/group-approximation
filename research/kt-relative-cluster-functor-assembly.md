---
rg: 2
id: kt-relative-cluster-functor-assembly
kind: claim
title: The Kun--Thom relative cluster functor is faithful once transported representatives improve
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Kun--Thom Theorem 4.1, imported by citation; this is the functor of its Lemma 4.3, assembled in the development for the unconditional proof of Theorem 4.1 from explicit finite hypotheses.
  kt-relative-functor-raw-map-defect-estimate: that bounds the defects of the raw map and carries estimate (7) back through the bridges; this builds the functor from improvements of the raw maps, proves faithfulness, and records estimate (7) for every representative of an image class.
artifacts:
  - GroupApproximation/KunThom/RelativeFunctorMetric.lean
  - GroupApproximation/KunThom/RelativeFunctorAssembly.lean
---

**ESTABLISHED, proved here, as an implication from explicit finite hypotheses.**
Modules `KunThom/RelativeFunctorMetric` and `KunThom/RelativeFunctorAssembly`,
namespace `GroupApproximation.GroupoidPresentation.ClusterMetric`.

**Setting.** This is Kun--Thom, arXiv:2608.06222v3, Lemma 4.3.
- A `ClusterMetric` on a groupoid presentation says three things:
  - representatives are partial bijections, and every pair of objects has a radius;
  - related representatives are closer than the radius, and representatives closer
    than eight radii are related;
  - the unit is the identity, composites are close to composed representatives, and
    self-defects are below the radius.
- Instances:
  - `ScaledPartialClusterSystem.clusterMetric`, with pair radius
    `2 * min (scale X) (scale Y)`;
  - `ScaledFinitePartialClusterData.clusterMetric`;
  - `FinitePartialClusterData.clusterMetric`, with constant radius.
- Data:
  - `R` is a set of retained objects of the source presentation, `D` a set of
    objects of the target presentation, and `obj : R → D` the object map, with
    `obj = π⁻¹` for the matching `π`;
  - `bridge X` is a partial bijection from the model of `X` to the model of `obj X`;
  - for a compressor, `bridge X = E.bridge u⁻¹ X (obj X)`.

**Proved.**
- `relativeFunctor : (P.restrict R).Obj ⥤ (Q.restrict D).Obj`.
  - A representative `b` goes to the class of a chosen improvement of the raw map
    `sandwich (bridge X) (bridge Y) b`.
  - `relativeFunctor_obj` gives `F X = obj X`, that is `F (π i) = i`.
- `relativeFunctor_faithful`.
- Estimate (7), `twoSidedDisagreement_sandwich_lt_of_ofRep_eq`: every representative
  of `F [b]` lies within `radius (obj X) (obj Y) + ρ X Y` of the raw map.
- `nonempty_hom_relativeFunctor`: connected retained objects have connected images.

**Hypotheses (open leaves of the assembly).**
- `himprove`: every raw map has an improvement within `ρ X Y`. For the scaled
  cluster groupoid it is produced by `ScaledPartialClusterSystem.repair_spec` from
  small defects of the raw map, which `kt-relative-functor-raw-map-defect-estimate`
  bounds.
- `hbridge`: the missing masses of `bridge X` are at most `β X`. It is produced by
  `RelativeFunctorEstimate.sourceDefect_add_targetDefect_bridge_le`.
- `hrespects`, `hcomp` and `hfaithful`: three families of linear inequalities in
  `ρ`, `β` and the radii. Each is required only between objects joined by a
  representative.

## Findings

1. **Radii belong to pairs.** The scaled cluster groupoid measures arrows from `X`
   to `Y` at `2 * min (scale X) (scale Y)`, with the gap at eight times that. No
   radius attached to the source alone satisfies both the nearness and the gap
   clauses when scales differ, so the interface carries a radius for each pair.
2. **Improvement of single arrows is required, and it exists.** The bridges
   intertwine transported labels with word labels, not generator labels. So the
   raw map is not a composite of two candidates, and the composite improvement
   `ImproveCloseAt` does not apply. The single-arrow repair `PairRepairAt` does.
3. **Choice of `ρ`.** Taking `ρ` equal to the target radius, the bound
   `repair_spec` gives directly, leaves `hcomp` within the 11/10 radius
   comparability of `8 · radius`. Taking `ρ` from the distance factor bound
   `d · card`, with `d → 0`, leaves all three families with slack.

Derivation: `kt-relative-cluster-functor-assembly-proof`.
