sec5-sentences lane report (clone lix-b), 2026-09-13

Target (ROSTER `## sec5-sentences`): every proof-step sentence of `sec:torsion-free` (tex 1621-1737).
- Rows 721da4c14d11 (L1698), 2d1cd22e5f49 (L1662), 2f997e5af4e6 (L1665) and bcc99703f838 (L1644).
- Re-grade a9dd4b90e479 (L1629).
- An `_of_fourLeaves` form for each `_of_leastAreaLeaves` sentence carrier.

## Landed

1. `GroupApproximation/Manuscript/NonMF/TorsionFreeSectionSentencesFourLeaves.lean`
   - LANDED 9f819ad8c; probe 0913-014453-61804 GREEN (base 9f819ad8c, md5 8470e2bacad5a46062fdd1c70385efea).
   - Unwired; queued for wiring together with `TorsionFreeSectionSentencesLeastArea`, which it imports.
   - It states four named propositions at the printed limit-set notion
     (`GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`):
     - `PrintedHullProofParagraph` (tex 1644-1648).
       - One target: `ker q = <<r>>_G` and `G/<<r>>_G ≃* Q`.
       - `m` targets: the quotient of the induction, with `φ(N)` suitable (clause (d)), `ker φ` the normal closure
         of at most `m` elements, and `Q` finitely presented when `G` is.
     - `PrintedSaturationPairAndHullAgain` (tex 1662-1665): `h₁, h₂ ∈ N` with `⟨h₁,h₂⟩` suitable with respect to
       `A' ⊇ A`, and the conclusion of `thm:hull` at `(A', N₀)` for every family `g`.
     - `PrintedSaturationApplyHull` (tex 1665-1667): a finite generating family `g` of `G` and the `thm:hull`
       quotient at `(A', N₀, g)`, with the kernel datum the proof uses at tex 1671-1672.
     - `PrintedTheoremApplySaturation` (tex 1698-1701): over `PrintedFournierFacioData G₀`, `lem:saturation` at `G₀`
       and `N` = the normal closure of `S = tJt⁻¹`.
   - Each proposition has `printedX_of_fourLeaves (hgreendlinger) (hbridge) : PrintedX` with `#audit_axioms`.
   - The hard direction of Osin's Theorem 1.1 enters as the closed
     `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet`.
2. Census rows L1644, L1662, L1665 and L1698 (partial) are in `metadata/nm-census-rows/sec5-sentences.tsv`.
3. Row a9dd4b90e479 (L1629) is already formalized by cite-hull.
   - Declaration: `HullCitationSentences.printedHullGeneratingSetLimitSet`, LANDED 18de0ce6a, probe 0912-105023-79191 GREEN.
   - `HullCitationSentences` is queued for wiring. No duplicate sec5 row was added.

## Residual Props

These two walls are the only open inputs of rows L1644, L1662, L1665 and L1698:
- hgreendlinger = `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`
- hbridge = `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}`

Kotowski-Ollivier and the finitely presented infinite simple group do not enter these sentences. When both producers
land, each `printedX_of_fourLeaves` becomes `theorem printedX : PrintedX` with `#audit_closed_axioms`, and the four rows
are re-graded formalized.

## `_of_leastAreaLeaves` sentence carriers and their four-leaves forms

- `TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_leastAreaLeaves` and
  `..._hullInductionOnTargetsGeneral_of_leastAreaLeaves` → `printedHullProofParagraph_of_fourLeaves` (this lane).
- In `TorsionFreeSectionSentencesLeastArea` (this lane):
  - `manuscriptSentence_saturationPairAndHullAgain_of_leastAreaLeaves` → `printedSaturationPairAndHullAgain_of_fourLeaves`;
  - `..._saturationApplyHullNoOmega_of_leastAreaLeaves` → `printedSaturationApplyHull_of_fourLeaves`;
  - `..._theoremApplySaturationNoOmega_of_leastAreaLeaves` → `printedTheoremApplySaturation_of_fourLeaves`.
- Covered by nm-endpoints' `TorsionFreeFourLeaves`:
  - `TorsionFreeHullPrintedLeastArea.manuscriptSentence_hullTheorem_of_leastAreaLeaves` → `printedHullTheorem_of_fourLeaves`;
  - `..._hullTheoremOsin_of_leastAreaLeaves` → `printedHullTheoremOsin_of_fourLeaves`;
  - `HullCitationSentences.manuscriptSentence_hullCommonQuotient_of_leastAreaLeaves` → `hullCommonQuotient_of_fourLeaves`.
- `TorsionFreeOsinNotion.manuscriptSentence_hullTheoremTorsionFreeOsin_of_leastAreaLeaves` is `thm:hull` over a
  torsion-free group at Osin's notion. The L1665 sentence it served is now `printedSaturationApplyHull_of_fourLeaves`
  at the printed notion. The `thm:hull` forms belong to nm-endpoints.

## Handed to hull-unbound (G-face merge for Osin Lemma 9.4, Case 2)

All of these are byte-identical to origin/main and have been removed from `sec5-sentences.files`:
- `GGT/VanKampen/SurgeryGFaceMergeMap.lean` and `GGT/VanKampen/SurgeryGFaceMerge.lean`.
- `GGT/VanKampen/SurgeryGFaceMergeDarts.lean`: 0528ed707, probe 0912-092624-73077 green.
- `GGT/VanKampen/SurgeryGFaceMergeRegions.lean`: 29a65f380, probe 0912-094255-56496 green.
- `GGT/VanKampen/SurgeryGFaceMergeMerged.lean` and `GGT/VanKampen/Estimating/OsinUnboundMerged.lean`: 8f7a8f1e1,
  probe 0912-100330-38574 green.
  - `Surgery.GFaceMerge.transportDistinguished` with its card/weight/avoid/unbound-dart lemmas;
  - `exists_unselectedGFacesMerged`.
- `GGT/VanKampen/Estimating/OsinUnboundReduced.lean`: 11850391a, probe 0912-102241-17531 green.
  - `exists_unselectedGFacesReduced(_of_faceCount)`.

The consumer is hull-unbound's `Estimating/OsinUnboundCaseTwo.lean`. The avoidance hypothesis everywhere is
`∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1`.

The predecessor's other 26 TorsionFree/HullSC/limit-set modules belong to nm-endpoints.

## W1 h94 helper: the oriented metric layer, with hull-count94

Assignment (team-lead, 2026-09-13): the monotone Morse index choice and `WordConnectorPair` with
`target_backward : b' < b`. `OsinLemma94RunInput.no_connector` is provable only in its oriented form.
hull-count94 keeps oriented Lemma 25, `OrientedSidePair`/`OrientedClassPair` and the oriented three-class lemma.

Both files LANDED at b1bd127ec. Probe 0913-025907-87619 GREEN (base b1bd127ec): both modules BUILT. Queued for wiring.
- `GGT/VanKampen/Estimating/UnboundMonotoneMorseIndex.lean`:
  - `vertex_take_prefix` and `isLambdaCQuasiGeodesicWord_take_prefix`;
  - `IsWordMorseRadius`, the inner statement of `exists_word_replacement_morse`;
  - `index_lt_of_prefix_near`: geodesic parameters `u + (3κ + 6δ) < u'` near vertices `a`, `a'` give `a < a'`;
  - `exists_word_replacement_morse_monotone`: one radius on the Cayley realisation at `δ + 6`;
  - `OsinUnboundScale.morse_gap_lt`: `3κ + 6δ < (λ√ρ/240 - c)/1000`.
- `GGT/VanKampen/Estimating/UnboundOrientedWordConnectors.lean`:
  - `OrientedWordConnectorPair` extends `WordConnectorPair` by `target_backward : b' < b`, with `targetWord_eq`;
  - `OrientedWordSidePair`, `.toWordSidePair` and `.exists_connectors`;
  - `OsinUnboundScale.orientedWordSidePair_of_parameters`: an antiparallel pair of long replacement segments
    (`β ≤ u' - u`, `β ≤ t - t'`, matched endpoints within `12(δ+1)`) gives an oriented word pair at `eps`.
  - `OsinUnboundScale.orientedWordSidePair_of_orientedClassPair` (LANDED 73caa3848; probe 0913-031106-30663 GREEN,
    bytes = origin/main; queued for wiring at 73caa3848): hull-count94's `OrientedClassPair` of the replacement
    polygon, at `(λ√ρ/240 - c)/1000` and `12(δ+1)`, gives `OrientedWordSidePair` at `eps`.

## Closed: the metric half of Osin's Lemma 9.4, oriented

`OsinLemma94AntiparallelMetricStatement` (hull-unbound's `OsinLemma94Pieces`) is proved, with `#audit_closed_axioms`.
- Both files LANDED: 779509227 and e3da1ba60.
- Probe 0913-034427-9910 GREEN (base 5f9c16b7b): both modules BUILT; the bytes equal origin/main.
- Queued for wiring after UnboundMonotoneMorseIndex, UnboundOrientedWordConnectors, OlshanskiiOrientedThreeClasses
  and OsinLemma94Pieces.
- `GGT/VanKampen/Estimating/UnboundOrientedWordPolygon.lean`:
  - `OsinUnboundScale.exists_orientedPolygonPair`: `exists_polygonPair` with `exists_orientedClassPair_of_aggregate_all`;
  - `unboundOrientedWordPolygonMonotone : UnboundOrientedWordPolygonMonotoneStatement` (closed):
    `UnboundWordPolygonMonotoneStatement` with the conclusion `OrientedWordSidePair`.
- `GGT/VanKampen/Estimating/OsinLemma94AntiparallelMetric.lean`:
  - `exists_component_dense_of_sideBudget`: `∑ k_i ≤ K n`, `K s < t` and `n t ≤ ∑ S_i` give `k_i s < S_i`;
  - `osinLemma94AntiparallelMetric : OsinLemma94AntiparallelMetricStatement` (closed).
    - The four-point Cayley graph is hyperbolic.
    - `unboundOrientedWordPolygonMonotone` is applied at `μ = 1`, with `ρ0 = (K+1)² ρ1` and `ρ' = ρ/(K+1)²`.
    - The pair comes from `OrientedWordSidePair.exists_connectors`, and `target_backward` gives `C.b' < C.b`.

The remaining input of `osinLemma94Section_of_pieces` is `OsinLemma94PlanarRunInput` (hull-unbound).

Collision: hull-count94 also wrote `OsinLemma94AntiparallelMetric.lean`, and its version overwrote the local file at 03:47.
- By 04:02 the local file was back to the bytes of e3da1ba60.
- hull-count94's probe 0913-035614-34211 still holds its own version. I asked it not to land that result at this path,
  since its file redeclares `OsinUnboundScale.exists_orientedPolygonPair`.

## W1 h94 planar half, with hull-unbound (team-lead, 2026-09-13 ~04:00)

Assignment: one case of `OsinLemma94PlanarRunInput`, the last residual of `osinLemma94Section_of_pieces`.
- hull-unbound owns the Prop and assigns the case. theoremc-retire takes Case 1 once hull-unbound hands it over.
- I have asked hull-unbound which case is mine, with its Lean name and file.
- Default, if there is no answer by the end of my next probe cycle: Case 2 in a new module of this lane, with no edits to
  hull-unbound's files.
  - Case 2 needs minimality of `∑ l(t_j)`, and `GloballyDistinguishedSectionFamily` has no field for it
    (theoremc-retire's finding).
  - The default measure is the dart count of the diagram.
- Census row L1636 (this lane) re-grades the note "planned producer `Estimating/OsinLemma94RunProducer.lean`
  (sec5-sentences)" on `osinLemma94Section_of_runInput` and `OsinLemma94RunInput`.
  - That module will not be built: `OsinLemma94Pieces` supersedes the run input.
  - The residual is `OsinLemma94PlanarRunInput`.

hull-unbound has been silent since 02:31, so the default stands (ROSTER): Case 2 goes to this lane, measured by dart count.

## Case 2 of Lemma 9.4: `OsinLemma94CaseTwoInput`

hull-unbound landed `Estimating/OsinLemma94PlanarPieces.lean` at 80790fad1.
- `osinLemma94Section_of_planarPieces` derives `OsinLemma94SectionStatement` from the closed metric half and four pieces:
  `OsinLemma94PolygonRealizationInput`, `OsinLemma94PolygonCountInput`, `OsinLemma94CaseOneInput` and
  `OsinLemma94CaseTwoInput`.
- It defines `GloballyDistinguishedSectionFamily.unboundSum`, `DartMinimal` (fewest darts among the optimal families with
  the same unbound sum) and `exists_dartMinimal`.
- This lane's piece is `OsinLemma94CaseTwoInput` (PlanarPieces:408), exactly as stated there.

`GGT/VanKampen/Estimating/OsinLemma94DartMinimal.lean`:
- First landed at 88db0df7b with its own `unboundSum`, `DartMinimal` and `exists_dartMinimal`. These collide with
  PlanarPieces, so its wire-queue entry was withdrawn at 07:10.
- Re-based on PlanarPieces: LANDED b6bda9923; probe 0913-074213-73156 GREEN (base 7283939e9), BUILT.
  Queued for wiring after `OsinLemma94PlanarPieces`.
- Declarations:
  - `Surgery.GFaceMerge.transportDistinguished_dartCount_add_two`, `PinchSplit.transportDistinguished_dartCount`;
  - `DartMinimal.false_of_dartCount_lt`;
  - `DartMinimal.unselectedGFacesMerged`: a dart-minimal family is merged across every edge between unselected G-faces;
  - `exists_reduced_dartCount_le(_of_faceCount)` and `exists_reduced_dartMinimal`.
- Retired, with no users: `OsinLemma94PlanarPolygons.ofUnboundSumEq`, `OsinLemma94PlanarRunInputReduced`,
  `osinLemma94PlanarRunInput_of_reduced` and `osinLemma94Section_of_planarRunInputReduced`.
- Census: a new L1636 row moves the 88db0df7b row onto `osinLemma94Section_of_planarPieces` and
  `OsinLemma94CaseTwoInput`.

Residual of this lane in W1 h94: `OsinLemma94CaseTwoInput.{u, w, v}`.

### Case 2 exchange (design, not yet in Lean)

Setup: `S` dart-minimal, `P : OsinLemma94RealizedPolygons S` maximal, and a backwards connector pair `C` (`C.b' < C.b`)
whose target side `t` on face `k` is a cutting side.
- Face `k` lies on both sides of every edge of `t`, and the inner vertices of `t` have degree two (`cutting_interior`).
- `target_long` gives `eps < b - b'`, and both connectors have length `< eps`.

1. Insert a connector `s` across face `k` (`GFaceSplitCorners.exists_split_corner_output`): +2|s| darts.
   - Use the start connector at `b` when `t⁻¹` lies in `walk[b, a]`, and the end connector at `b'` otherwise.
2. Merge across the edge of `t` next to the connector, whose sides are now the two new faces (`Surgery.GFaceMerge`):
   −2 darts.
3. Delete the rest of `t` toward its nearer end as spikes, tip first: −2 darts each.
   - That stretch together with the merged edge has at least `b - b'` edges.

Net change: `2(|s| - ℓ) < 0` darts with `ℓ ≥ b - b' > eps > |s|`. Cells, the exterior and the selected regions are
untouched, so the family transports with the same unbound sum, against `DartMinimal`. The insertion needs `s ≠ []`, so
an empty connector is a separate case.

Still missing in Lean:
- transport of distinguished families across the insertion: respects, nondegenerate, labelLegal, reduced, `S`, darts;
- `SurgerySpikeDeletion*`: a diagram-level spike deletion (a dart fixed by `sigma`, on an unselected G-face) with region
  transport and dart count −2;
- the walk and corner combinatorics of steps 1-3.

## Next

1. `GGT/VanKampen/SurgerySpikeDeletion*.lean`:
   - the map layer: kept faces off the spike face, and a shrunk face that reads the old walk without the two spike darts;
   - the diagram surgery and the region transport, modelled on `SurgeryGFaceMerge*`.
2. Transport across `GFaceSplitCorners`, then `Estimating/OsinLemma94CaseTwo.lean` with
   `osinLemma94CaseTwo : OsinLemma94CaseTwoInput`.
3. Watch origin/main for closed producers of the two walls. When both land, flip the four forms to closed endpoints and
   re-grade the rows formalized.
