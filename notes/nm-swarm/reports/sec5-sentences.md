sec5-sentences lane report

G-face merge for Osin Lemma 9.4, Case 2 (edge deletion between two G-faces)

1. GGT/VanKampen/SurgeryGFaceMerge.lean: the merge `R.diagram`, darts `keep`/`val`, faces
   `kept`/`merged`, relator cell map, O-equivalence, reducedness, legal labels. Compiled.
2. GGT/VanKampen/SurgeryGFaceMergeDarts.lean: darts off the deleted edge, `faceSet s = s.image
   kept`, face boundaries and relator-cell darts through `keep`, `invDarts_map`, `dartWord_map`,
   `reverseDarts_mapTo`, `targetBoundaryDarts_map`. Landed 0528ed707, probe 0912-092624-73077
   green (base 229dffbda). In the root-wiring wave: edits to it or its imports land NM_ATTIC
   until a probe is green.
3. GGT/VanKampen/SurgeryGFaceMergeRegions.lean: transport of face-set boundaries, shellings and
   contiguity geometry across the merge; `regionFamily` with card, weight, pairwise, faces,
   profile and avoid-merged; unbound darts of each relator cell through `keep`
   (`unboundDarts_eq`, `unboundDarts_card`, `sum_unboundDarts_card`); `transportSection` with
   weight, card, nondegenerate and legal labels. Landed 29a65f380, probe 0912-094255-56496
   green (base f9eaa73be, md5 646b9712cfd3be55336033111489e9b1). Orphan; consumed by
   hull-unbound.

The avoidance hypothesis everywhere is `∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1`.
