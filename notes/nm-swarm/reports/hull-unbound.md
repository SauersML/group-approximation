# hull-unbound lane report

## Scope
Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), `OsinLemma94SectionStatement` in
`Estimating/OsinAppendixSections.lean`. This lane covers the surgery contradictions against
`weight_maximal`, which show that unbound darts of relator cells are rare. The counting layer
from those facts to `∑ unboundDarts card < n √ρ` is offered to hull-respell as a named-Prop
reduction.

## On main
- `Estimating/SingletonFaceRegion.lean` (bd53291cd, compiled): `ContiguityGeometry.ofSingletonFace`,
  `RegionCandidate.familyWeight_lt_cons_singleton`, `cons_singleton_pairwise`.
- `GFaceQuadrilateralRegion.lean` (64e1a784f), `Estimating/OsinUnboundCaseOne.lean`
  (c657430ef, then ccde452ae against nondegenerate section families, compiled):
  `RealizedSectionFamily.false_of_quadrilateral_region`,
  `RegionCandidate.respectsSections_of_sameTargetProfile`.
- `SurgeryFaceEdgeDoubling.lean` (ceb7135c3, compiled): `FaceEdgeDoubling.diagram`, `oEquivalent`,
  `reduced`, `label_admissible`, `boundary_digon`, `boundary_digon_value`.
- `SurgeryFaceEdgeDoublingRegions.lean` (b67574c33, compiled, in the root-wiring wave, so it lands
  NM_ATTIC): `FaceEdgeDoubling.regionFamily`, with `_weight`, `_pairwise`, `_profile` and `_faces`.
- `Estimating/OsinUnboundSharedEdge.lean` (707c06d58, landed unverified, probe running):
  ```lean
  theorem SectionCuts.exists_section_of_lt (cuts : SectionCuts D lambda c word) {p : ℕ}
      (hp : p < word.length) :
      ∃ j : Fin cuts.count, cuts.cut j.castSucc ≤ p ∧ p + 1 ≤ cuts.cut j.succ
  theorem RealizedSectionFamily.false_of_unbound_shared_edge
      (S : RealizedSectionFamily D lambda c eps Delta cuts)
      (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
      (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
        other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
          other.weight ≤ S.weight)
      (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
      (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart)
      (hd : d ∈ RegionCandidate.unboundDarts S.family i)
      (hlen : 1 < (cellDarts S.diagram i).length)
      (hadj : (∃ i₂ : Fin S.diagram.rCellCount,
          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = (cell S.diagram i₂).face) ∨
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace) :
      False
  ```

## Next (reserved names)
- `Estimating/OsinUnboundMerged.lean`: the quadrilateral contradiction after merging the adjacent
  G-face, via sec5-sentences' `GFaceMerge.transportSection` (SurgeryGFaceMergeRegions, 29a65f380).
- `Estimating/OsinUnboundCaseTwo.lean`: Case 2 (vertex splitting), via fff-periodic's
  `PinchSplit.transportDistinguished` (SurgeryPinchSplitExtremal, c48fbb6c7).

## Coordination
- sec5-sentences owns `SurgeryGFaceMerge*`; fff-periodic owns `SurgeryPinchSplit*`.
- hull-respell is offered the counting reduction to `OsinLemma94SectionStatement` from a named
  geometric run Prop.
