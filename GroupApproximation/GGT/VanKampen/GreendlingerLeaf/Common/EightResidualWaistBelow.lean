import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.EightResidualWaist
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.CellStepBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist over eight residuals, with the cell step below the inductive bound

This is `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`
(`GreendlingerLeaf/Common/EightResidualWaist`) with residual 06 in its below form,
`CellPocketOuterPinchStepSectionDistinctBelowStatement` (`GreendlingerLeaf/Common/CellStepBelow`).
The step is consumed only inside binder 5 below the inductive bound, so the premise
`OsinLemma97Below … X.rCellCount` is available there; the pinch below the bound
(`cellPocketPinchSectionDistinctBelowStatement_of_outerPinchStepBelow`) feeds
`osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler`.  Every other
argument is as in the eight-residual waist.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`: pieces 01, 04, 05, 06 below
  the bound, and 07–10 give `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.4, 9.7 and
4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from eight leaf residuals, with the cell step below the
inductive bound**: as `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`, with the
outer-pinch cell step assuming clause (b) of Lemma 9.7 below the number of relator cells. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwocopy : OsinTwoGonCleanCopySectionStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hwhole : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow
    (osinLemma94Section_of_classCountTwoThreshold
      (osinLemma94ClassCountInput_of_endLoops (osinLemma94ClassEndLoopsInput_of_budget hbudget)
        (osinLemma94SameCellFactorInput_of_scan
          (osinLemma94SameCellScanInput_of_pocket
            (osinLemma94SameCellPocketInput_of_loopCut sameCellPocketCellFreeValue
              sameCellPocketLoopCut))))
      (osinLemma94ClassCasesTwoThreshold_of_residuals
        (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk osinLemma94CaseOneSameCell)
        osinLemma94CaseTwoInput hspan))
    (osinMultipleEdgeCutBelowSection_of_copyPieces
      (osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler
        cellPocketCopyCleanBothOrders cellPocketWalkOuterOffSideSomeOrder
        cellPocketWalkEuler
        (cellPocketPinchSectionDistinctBelowStatement_of_outerPinchStepBelow hcellStep) hproper)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection
      (osinTwoGonHoldsSection_of_cleanCopyEuler htwocopy osinTwoGonDecompositionEulerSection))
    (osinSectionPocketCutSection_of_residualsTwoArc
      (osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection hfaces hwhole)
      (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow
