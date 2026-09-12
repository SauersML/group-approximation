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
   green (base f9eaa73be, md5 646b9712cfd3be55336033111489e9b1). In the root-wiring wave
   bo6h618iu: edits to it or its imports land NM_ATTIC until a probe is green.
4. GGT/VanKampen/SurgeryGFaceMergeMerged.lean: `faceOf_val_of_merged`;
   `merged_noInternalFaceDart (hsingle)`, where the deleted edge is the only edge with both
   sides on `R.first`/`R.second`; `merged_noInternalFaceDart_of_sides (h1 h2 hedge)`. Landed
   8f7a8f1e1, probe 0912-100330-38574 green (base e04551169, md5
   a22f9c50179dab51523abf9989a0df2c). Orphan.
5. GGT/VanKampen/Estimating/OsinUnboundMerged.lean (handed over by hull-unbound):
   `Surgery.GFaceMerge.transportDistinguished` with `_toRealizedSectionFamily`, `_diagram`,
   `_family` (rfl), `_weight`, `_card`, `_avoid_merged`, `_sum_unboundDarts_card`,
   `_faceCount_add_one`; `GloballyDistinguishedSectionFamily.UnselectedGFacesMerged` and
   `exists_unselectedGFacesMerged` (same card and total unbound darts, by strong induction on
   the face count). Landed 8f7a8f1e1, probe 0912-100330-38574 green (md5
   7379104203e2c360a0fda7d935cc87a4). Orphan; consumed by hull-unbound's OsinUnboundCaseTwo.

The avoidance hypothesis everywhere is `∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1`.
