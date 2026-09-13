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

## Next

Watch origin/main for closed producers of the two walls. When both land, flip the four forms to closed endpoints and
re-grade the rows formalized.
