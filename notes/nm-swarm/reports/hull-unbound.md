# hull-unbound lane report

## Scope
Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), `OsinLemma94SectionStatement` in
`Estimating/OsinAppendixSections.lean`. This lane covers the surgery contradictions against
`weight_maximal`, which show that unbound darts of relator cells are rare. hull-count94 owns the
counting layer from those facts to `∑ unboundDarts card < n √ρ`. This lane produces its run Prop.

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
- `Estimating/OsinUnboundSharedEdge.lean`: the first landing (707c06d58) was red because `set` on
  `S.diagram` shadowed dependent hypotheses. It was rewritten without `set` as b52365364 (landed
  unverified, probe running). Helpers: `FaceEdgeDoubling.unitArc`, `unitArc_darts`,
  `invDarts_carrierImage_self_dart`, `invDarts_embedding_alpha`.
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

## Case 2 inputs (sec5-sentences)
- `Estimating/OsinUnboundMerged.lean` (8f7a8f1e1, PROBE GREEN 0912-100330-38574):
  `Surgery.GFaceMerge.transportDistinguished`, `GloballyDistinguishedSectionFamily.UnselectedGFacesMerged`,
  `exists_unselectedGFacesMerged`, `GFaceMerge.merged_noInternalFaceDart`.
- `Estimating/OsinUnboundReduced.lean` (11850391a, PROBE GREEN 0912-102241-17531):
  `PinchSplit.transportDistinguished_sum_unboundDarts_card`,
  `PinchSplit.transportDistinguished_faceCount_add_one`,
  `GloballyDistinguishedSectionFamily.UnselectedPinchesSplit`, `exists_unselectedGFacesReduced`.

## Next (reserved names)
- `Estimating/OsinUnboundCaseTwo.lean` (this lane): after `exists_unselectedGFacesReduced`, an
  unbound dart of a relator cell whose reverse lies on an unselected G-face gives the quadrilateral
  region consumed by `false_of_quadrilateral_region`.

## Coordination
- sec5-sentences owns `SurgeryGFaceMerge*`, `Estimating/OsinUnboundMerged.lean` and
  `Estimating/OsinUnboundReduced.lean`. fff-periodic owns `SurgeryPinchSplit*`.
- hull-count94 owns `Estimating/OsinLemma94RunInput.lean` and `Estimating/OsinLemma94Counting.lean`.
  hull-respell declined the counting reduction.
