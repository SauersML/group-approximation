# hull-unbound lane report

## Scope
Integrator of h94: the closed `theorem osinLemma94Section_closed : OsinLemma94SectionStatement`
(Osin, arXiv:math/0411039v3, §9, Lemma 9.4, in `Estimating/OsinAppendixSections.lean`). This lane
owns the planar half (Cases 1 and 2 against `weight_maximal` and cut minimality). The pieces follow.

## Piece Props (landed)
`Estimating/OsinLemma94Pieces.lean` (b8441172e, landed unverified, probe running):
```lean
theorem osinLemma94Section_of_pieces
    (hmetric : OsinLemma94AntiparallelMetricStatement.{u, w})
    (hrun : OsinLemma94PlanarRunInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v}
```
- `OsinLemma94AntiparallelMetricStatement` (metric half, proposed owner hull-count94): for
  four-point hyperbolic `D`, `0 < λ`, `0 ≤ c` and every side constant `K`, monotone thresholds
  with `OsinLemma94DensePolygonsAntiparallel D λ c ε ρ K`. Closed quasi-geodesic word polygons
  with `∑ sides ≤ K n` and `n √ρ ≤ ∑ classWordLength` have
  `∃ k, ∃ C : WordConnectorPair .., C.b' < C.b`.
- `OsinLemma94PlanarRunInput` (planar half, this lane): under the Lemma 9.4 hypotheses there is a
  `K` and monotone thresholds with `Nonempty (OsinLemma94PlanarPolygons D λ c ε K S)`. The fields
  are `side_budget`, `closed`, `step`, `quasiGeodesic`, `short`, `covers` and `no_antiparallel`.
  The model test is `OsinLemma94PlanarPolygons.ofNoUnbound`.

## Finding: connector orientation
- `WordConnectorPair` fixes `a < a'` and leaves `b`, `b'` in either order. The landed metric chain
  keeps no orientation: `SidePair` says "Orientation on either side is immaterial", and
  `exists_long_close_pair` ends with `β ≤ |s' - s|`.
- Cases 1 and 2 draw both connectors as chords of one face, and the chords `{a, b}` and `{a', b'}`
  are disjoint exactly when `b' < b`. So `OsinLemma94RunInput.no_connector`, which forbids both
  orientations, is more than the source proves. hull-count94 found the same (674b1b428).
- One constant `K` replaces `53` and `4`, since Steiner corners may push `k_i` above `4 n_i`.

## On main (surgery layer)
- `Estimating/SingletonFaceRegion.lean` (bd53291cd, compiled): `ContiguityGeometry.ofSingletonFace`,
  `RegionCandidate.familyWeight_lt_cons_singleton`, `cons_singleton_pairwise`.
- `GFaceQuadrilateralRegion.lean` (64e1a784f), `Estimating/OsinUnboundCaseOne.lean` (ccde452ae,
  compiled): `RealizedSectionFamily.false_of_quadrilateral_region`,
  `RegionCandidate.respectsSections_of_sameTargetProfile`.
- `SurgeryFaceEdgeDoubling.lean` (ceb7135c3, compiled) and `SurgeryFaceEdgeDoublingRegions.lean`
  (b67574c33, compiled): `FaceEdgeDoubling.diagram`, `regionFamily` and its transports.
- `Estimating/OsinUnboundSharedEdge.lean` (b52365364, landed unverified, in the running probe):
  `SectionCuts.exists_section_of_lt`, `RealizedSectionFamily.false_of_unbound_shared_edge`.

## Case 2 inputs (sec5-sentences)
- `Estimating/OsinUnboundMerged.lean` (8f7a8f1e1): `GloballyDistinguishedSectionFamily.UnselectedGFacesMerged`,
  `exists_unselectedGFacesMerged`.
- `Estimating/OsinUnboundReduced.lean` (11850391a): `UnselectedPinchesSplit`,
  `exists_unselectedGFacesReduced`, which keeps the family card and the unbound sum.

## Next
- The second-level split of `OsinLemma94PlanarRunInput`: component polygons realized on the face
  walks of a reduced family, Case 1 through `false_of_quadrilateral_region`, and Case 2 by exchanging
  a bridge path for a connector.
- `osinLemma94Section_closed` once both halves close. Then help hull-respell with hgreendlinger.

## Coordination
- hull-count94 owns `Estimating/OsinLemma94RunInput.lean` and `Estimating/OsinLemma94Counting.lean`.
  Both are superseded by the pieces above and have no users. The lead is asked to point hull-count94
  at `OsinLemma94AntiparallelMetricStatement`.
- sec5-sentences owns `SurgeryGFaceMerge*`, `OsinUnboundMerged` and `OsinUnboundReduced`.
  fff-periodic owns `SurgeryPinchSplit*`.
