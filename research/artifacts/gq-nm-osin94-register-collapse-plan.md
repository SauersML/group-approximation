# Osin 9.4 register lines: they collapse with hG (lane nm-osin94)

Read against origin/main 1fbca671a7 on 2026-09-19, source only and not built.

## Finding

- The conditional register `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` has 31 live lines.
- 29 of them (28 distinct declarations) are cited only by census rows **8aead549f1fe** and **4895f03fdf5f**. Both are `thm:hull` (tex l.2135) and both are graded partial.
- Each of the 28 declarations is a piece of an *alternative route to the same statement*, `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` (hG, Osin's Lemma 4.4 at least-area diagrams). The Osin V2 route `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2` (`Estimating/OsinGreendlingerResidualsV2.lean`) consumes them with six residuals.
- None of them is independent of hG, so there is nothing to prove in this register apart from hG itself.
- Three routes to hG are on main:
  1. **GL06** (`Full.GL06.relativeGreendlinger_zero_of_allCells_of_core`) has two residuals, `GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement` and `GL03DKept.gl03dKept_KeptSubwalkCoreStatement`. These are the lanes nm-gl06e and nm-gl03d.
  2. **Osin V2** has six residuals.
  3. **Below waist**: `GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed_of_liveFrontier` has four live leaves.
- Closing hG by **any** route removes all 29 lines, through the regrade below.

## Regrade once hG is closed (census path, run on MSI)

1. Add a closed form of each of the 16 `*_of_greendlinger` declarations cited by both rows. Each is `X_closed : T := X_of_greendlinger hG_closed`; every one takes hG as its only hypothesis (checked).
   - Alternatively, cite the closed forms of lane gl-assembly-05 (`Manuscript/NonMF/GreendlingerClosedHull/*`, `*_of_openResidualsBelow` applied to closed residuals).
2. In `metadata/NON_MF_SENTENCE_MAP.tsv`, rows 8aead549f1fe and 4895f03fdf5f:
   - replace each `*_of_greendlinger` with its closed form;
   - **drop** the Osin-9.4 declarations listed below. They belong to routes the closed proof does not use, and the printed sentence is the statement of `thm:hull`, not Osin's proof.
   - Keep every other cited declaration.
3. Delete the matching register lines. The gate fails on a line that matches nothing, so leaving them is not an option.
4. Regenerate the census with `scripts/sentence_census.py` on MSI. Expected: both rows move to *formalized*.
5. `HullSC.quotientPeripheralLetterPullbackStatement_holds` and `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` are registered as "buried-conditional ... not a conditional". They are closed and the closed route uses them. If the rows still cite them, their two lines stay; they are classifier false positives, not debt.

## The 28 declarations (29 register lines)

- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.alpha_not_mem_of_dartMinimal`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.BoundaryArcsQuasiGeodesic`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.CellArcsQuasiGeodesic`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.chainRespellInput_of_pieces`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.CuttingChainsQuasiGeodesic`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.DartMinimal`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.DartMinimal.unselectedGFacesMerged`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.GFacesApart`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.gFacesApart_of_dartMinimal`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.not_leaf_of_dartMinimal`
- `GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant`
- `GroupApproximation.GGT.VanKampen.osinLemma94CaseTwo_false`
- `GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.dense_of_classCovers`
- `GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.unbound_lt_of_classes`
- `GroupApproximation.GGT.VanKampen.osinLemma94CuttingChainsInput_of_pieces`
- `GroupApproximation.GGT.VanKampen.OsinLemma94PinchedQuadrilateralStatement`
- `GroupApproximation.GGT.VanKampen.OsinLemma94PinchedQuadrilateralStatement.false_of_quadrilateral`
- `GroupApproximation.GGT.VanKampen.OsinLemma94PlanarPolygons.unbound_lt`
- `GroupApproximation.GGT.VanKampen.OsinLemma94PlanarRunInput`
- `GroupApproximation.GGT.VanKampen.OsinLemma94PolygonCountInput`
- `GroupApproximation.GGT.VanKampen.osinLemma94PolygonCountInput_of_sideBudget`
- `GroupApproximation.GGT.VanKampen.osinLemma94PolygonCoversInput`
- `GroupApproximation.GGT.VanKampen.OsinLemma94PolygonSideBudgetInput`
- `GroupApproximation.GGT.VanKampen.osinLemma94Section_of_pieces`
- `GroupApproximation.GGT.VanKampen.osinLemma94Section_of_planarPieces`
- `GroupApproximation.GGT.VanKampen.osinLemma94Section_of_residuals`
- `GroupApproximation.HullSC.quotientPeripheralLetterPullbackStatement_holds`
- `GroupApproximation.HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`

## The 16 `*_of_greendlinger` declarations cited by both rows

- `GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientStatement_of_greendlinger`
- `GroupApproximation.HullSC.hullBallFormStatementGeneral_of_greendlinger`
- `GroupApproximation.HullSC.hullCanonicalQuotientStatementGeneral_of_greendlinger`
- `GroupApproximation.HullSC.hullOneStepStatement_of_greendlinger`
- `GroupApproximation.HullSC.hullOneStepStatementGeneral_of_greendlinger`
- `GroupApproximation.HullSC.hullTowerStatementGeneral_of_greendlinger`
- `GroupApproximation.HullSC.torsionFreeHullCanonicalQuotientStatement_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.hullSmallCancellationTorsionFreePrinted_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptHullTheoremLimitSet_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheorem_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms.manuscriptSentence_hullTheoremOsin_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.hullSmallCancellationTorsionFreePrinted_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheorem_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremLimitSet_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf.printedHullTheoremOsin_of_greendlinger`
- `GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerSentences.manuscriptSentence_hullTheoremTorsionFreeOsin_of_greendlinger`
