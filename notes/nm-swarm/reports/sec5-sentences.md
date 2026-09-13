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

### Spike deletion (landed, used by the removal pieces)

The first design inserted a connector, merged one edge and deleted the rest of `t` as spikes. The spike deletion landed
and is queued for wiring:
- `SurgerySpikeDeletionMap` 3c672277a, `SurgerySpikeDeletion` 14daf9b00, `SurgerySpikeDeletionDarts` 31982031d,
  `SurgerySpikeDeletionRegions` 0838416d4, `Estimating/OsinLemma94SpikeTransport` ba4233ef8.
- jacobson's `OsinLemma94PendantRemoval` (61c2ade8e) builds on it, and hull-unbound's
  `separatingPathRemovalInput_of_pendant` (7d4a2515f) builds on that.

### Case 2 in Lean: windows, insertion, removal

`GGT/VanKampen/Estimating/OsinLemma94CaseTwo.lean`: LANDED 52b77f408; probe 0913-130606-76787 GREEN, BUILT.
- `CaseOneWalk.polygon_four_windows`: from some corner the face walk reads `X ++ q ++ Y ++ p`, with `q` the target
  segment from `b'` to `b` and `p` the source segment from `a` to `a'`.
- No reverse dart of `q` lies in `q` (hull-unbound's `alpha_not_mem_of_dartMinimal`, 26b30e5df). None lies in `p`,
  since the reverse darts of an (A1) arc lie on a relator cell.
- The walk across `q` runs back along it (`cutting_interior`), and the walk does not jump over `q` or `p`
  (`CaseTwoWalk.facePerm_mem_front_of_not_mem_back`). So the reverse darts of `q` all lie in `X` or all lie in `Y`.
- Insert the end connector (reverse darts in `X`) or the start connector (in `Y`) across the face with
  `SeparatedCornerInsertionInput`. This adds at most `2 |s|` darts, and `q` then runs between two different unselected
  G-faces.
- Remove `q` (`separatingPathRemovalInput_of_pendant`), which takes away `2 (b - b')` darts.
- `|s| < ε < b - b'` (`target_long` with `wordDist_vertex_le'`), against `DartMinimal`.

Declarations:
- `CaseTwoWalk.rotate_add_length_of_eq`, `getElem_of_last_of_step`, `facePerm_mem_front_of_not_mem_back`,
  `runsBackAcross_window`;
- `osinLemma94CaseTwo_false (hinsert) (heps : 3 ≤ eps) (hS : S.DartMinimal) P k C hback hcut : False`;
- `osinLemma94CaseTwoInput_of_insertion (hinsert) : OsinLemma94CaseTwoInput`, with `ε₀ = 3` and `ρ₀ = 1`;
- `osinLemma94CaseTwoInput : OsinLemma94CaseTwoInput` (closed, `#audit_closed_axioms`). It applies the previous theorem
  to sec2-sentences' `GloballyDistinguishedSectionFamily.separatedCornerInsertionInput`
  (`Estimating/OsinLemma94SeparatedInsertionProof`, 619b70139). LANDED e0e94015d; probe 0913-131149-5355 GREEN, BUILT;
  queued for wiring.

`GGT/VanKampen/Estimating/OsinLemma94SeparatedInsertion.lean` states
`GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput`.
- LANDED b52230097; probe 0913-113234-56193 GREEN, BUILT.
- Queued for wiring after `OsinLemma94ChainRespell`.

Case 2 needs no same-cell competitor (no loop candidate, LoopCut ruling A) and no `ChainRespellInput`.

## Residual Props of Case 2

None. sec2-sentences proved `GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput.{u, w, v}` (619b70139), so
`OsinLemma94CaseTwoInput` is closed. The other pieces of `osinLemma94Section_of_planarPieces` are still conditional:
- `OsinLemma94PolygonRealizationInput` on `OsinLemma94PolygonPartitionInput` (`osinLemma94PolygonRealizationInput_of_partition`);
- `OsinLemma94PolygonCountInput` on `OsinLemma94PolygonSideBudgetInput` (`osinLemma94PolygonCountInput_of_sideBudget`);
- `OsinLemma94CaseOneInput` on `OsinLemma94CaseOneWalkStatement` and `OsinLemma94CaseOneSameCellStatement`.

Census: a new L1636 row (partial) records the closed Case 2 piece.

## The polygon partition: covered by ghw-assembly

Assignment (team-lead, 2026-09-13 ~13:15): take one open piece of `OsinLemma94PolygonPartitionInput`, either the face
enumeration or the `walk` and `cutting_interior` fields.
- I asked ghw-assembly and cite-hull at ~13:17 which piece was free.
- By 13:21 ghw-assembly had written the whole Prop in its lane file `Estimating/OsinLemma94PolygonPartition.lean`
  (unlanded). It defines `realizedPolygons` with every field and proves `realizedPolygons_maximal` and
  `osinLemma94PolygonPartitionInput`. `OsinLemma94PolygonMaximal` LANDED 9f03bfcd3.
- My draft (`UnselectedFaces`, `polygonCount`, `polygonFace_complete`) duplicated `polygonFace` and
  `exists_polygonFace` there. It stays in scratch and was never landed or probed.
- sec5-sentences stood down and told ghw-assembly, cite-hull and main (~13:25).

The partition LANDED at 746028b24 (ghw-assembly).

## The count piece of Lemma 9.4, with hull-count94 (team-lead, 2026-09-13 ~13:30)

Assignment: `OsinLemma94PolygonCountInput`, one of the two open hypotheses of `osinLemma94Section_of_residuals`, split
with hull-count94. `OsinLemma94CaseOneInput` stays with theoremc-retire, ko-closed and jacobson.
- hull-count94's plan has two steps.
  1. The rest of the ruling: skip-arc (A2) sides, the `Maximal` skip clause, the A1-filtered budget and a pinch
     exclusion. These land with the Case 1 users.
  2. The respelled side budget, proved from the Lemma 9.3 counts on main (`PhiPrimeCountInput`, `CellFaceCountInput`).
- I offered hull-count94 step 2 (~13:31) and asked for the target Prop, its file and the spelling.
- audit-intro's model test is back (0c95c8298), and main has ruled (ROSTER 13:05-13:40):
  - a class is a maximal run of consecutive `.cell j` sides whose gaps read words of value one;
  - a one-sided bubble (exactly one class, of kind (A1)) is dropped, and the budget sums only over polygons with an
    (A1) side;
  - the class word is the `dartWord` of the reversed cell arc, gaps included, and `L = 24ε + 2(K+24)⌈(c+2)/λ⌉`.
  The respelled `SideBudget` is hull-count94's step 1 and is not on main yet.
- I sent hull-count94 the step-2 finding below and proposed a split (msg 7ca57652): hull-count94 writes the
  respelling, and this lane writes the diagram-level class count. No reply yet.

Groundwork:
- The covering half is closed (`osinLemma94PolygonCoversInput`, 2b2e16cc6). The residual is
  `OsinLemma94PolygonSideBudgetInput` (`Estimating/OsinLemma94PolygonCount.lean:81`), with
  `SideBudget P K := ∑ k, P.sideCount k ≤ K n` (PlanarPieces:217).
- The binders give `|M| ≤ 3(n + r − 1)` and `DartMinimal`, and `cuts.count_le` gives `r ≤ 4`.
- Short sides, LANDED. `GGT/VanKampen/Estimating/OsinLemma94ShortSides.lean`: LANDED 4b6dd3cd8; probe
  0913-135154-29800 GREEN (base e0dcf8b99), BUILT; queued for wiring after `OsinLemma94PlanarPieces` and
  `OsinLemma94RegionSideCount`. It does not depend on the budget spelling. It is Osin's "Clearly the number of arcs of
  type (A3) is at most 2|M|", at the level of polygon sides.
  - `OsinLemma94RealizedPolygons.shortSides`, `faceOf_of_mem_sideDarts`, `sideDarts_disjoint`;
  - `alpha_mem_sides_of_short`: the reverse of a dart of a short side lies on a side of a selected region (it is on
    neither contiguity arc, since the polygon's face is no relator cell, and not on `∂Δ`);
  - `sum_card_shortSides_le`: `∑ k, #(shortSides k) ≤ 2 ε |M|`;
  - `sum_card_shortSides_le_mul`: `≤ 24 ε n` from `0 < n` and `|M| ≤ 3(n + r − 1)`.
- (A1) and (A2) sides. I found no diagram-level producer of Lemma 9.3's `#A1 + #A2 ≤ 2|M| + n + r`:
  `ComplementaryComponents.typeA12_le` is a structure field with only a zero model, and `lemma61_arcCount_le` is only
  its arithmetic. So step 2 has to count the maximal unbound runs on cells and sections itself. My reading is that
  each side end is charged to a region end, a whole cell, a whole section or a touching vertex. The touching vertices
  (pinches, cells meeting at a vertex) are what the pinch exclusion and the skip clause have to remove.
- Cutting sides have the polygon face on both sides of every dart (`cutting_internal`).
- `GFacesApart`: two unselected G-faces across one edge are the same face.

Stage B (ROSTER l.844-845): hull-count94's module `OsinLemma94PolygonClasses` has `ClassBudget` (over polygons with an
(A1) class and at least two classes) and `ClassCovers`.
- Helpers: audit-intro (short-side count), this lane (`ClassBudget` from the 9.3 run counts) and hull-component (the
  gap-length lemma `QuasiGeodesicValueOneGap`, a3169d05f, and the bubble accounting).
- The short-side count had already landed here. I told audit-intro (~14:00) so it is not written twice.
- audit-sec3's wrap-pair note (l.825): a run can split at the base of the face walk, at most one extra class per polygon.

## Option (2): the one-cell conjunct of the metric Prop (gate confirmed ~14:05)

ROSTER l.779 and l.812-815: the Dense respelling adds a one-cell conjunct at `λ⁻¹(ε + c)`. It is gated on this lane
confirming that the metric proof delivers it. Confirmed to main and hull-unbound:
- F1's order is on main (Pieces:97, 9f8779c4e), and `osinLemma94AntiparallelMetric` proves it.
- The pair's vertices are within the Morse radius `κ` of segment points at distance `≥ β = (λ√ρ'/240 − c)/1000`, so
  `d(a,a') ≥ β − 2κ` and `d(b,b') ≥ β − 2κ` (`nearby_endpoints_keep_shortening_margin` is only the triangle inequality).
- One more `exists_nat_sqrt_threshold λ c (1000(L + 2κ))` in the ρ₀ of `unboundOrientedWordPolygonMonotone` gives
  `L < d(a,a')` and `L < d(b',b)` for any `L` fixed before ρ₀. The metric proof uses the scale at `ρ' = ρ/(K+1)² ≥ ρ₁`.
- Proof side, this lane's files: `UnboundOrientedWordConnectors`, `UnboundOrientedWordPolygon`,
  `OsinLemma94AntiparallelMetric`. The spelling is hull-unbound's (Pieces). I asked hull-unbound for it.
- Users of `OsinLemma94DensePolygonsAntiparallel` to co-probe: Pieces, PlanarPieces, `OsinLemma94AntiparallelMetric`,
  `OsinLemma94SectionResiduals` (importer) and hull-component's unlanded `OsinLemma94BudgetFilter`
  (`exists_of_budget_on`), which is not in hull-unbound's Rule 22 list.

## Next

1. On hull-unbound's spelling: write the proof side of option (2) and co-probe it with the users above.
2. `ClassBudget` from the 9.3 run counts, on hull-count94's `OsinLemma94PolygonClasses` spelling, with
   `sum_card_shortSides_le_mul` for the short sides. Waiting for its reply on the split (msg 7ca57652).
2. Watch origin/main for closed producers of the two walls. When both land, flip the four forms to closed endpoints and
   re-grade the rows formalized.
