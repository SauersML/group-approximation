import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV8Closures
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellClosed
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist over eight residuals

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4.  This is the body of
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8` (`Estimating/OsinGreendlingerWaistV8`),
re-spelled so that it only applies closed theorems.  Two of the ten residuals of
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures` drop out:

* piece 02, `SameCellPocketLoopCutStatement`, is supplied by the closed `sameCellPocketLoopCut`
  (`Estimating/OsinUnboundSameCellPocketLoopCut`);
* piece 03, `EnclosedSubdiagramLoopCutSuccStatement`, is no longer consumed.  In V8 it enters, together
  with `closedWalkEnclosedSubdiagramSucc`, only through the Case 1 same-cell subterm
  `osinLemma94CaseOneSameCell_of_rCell (…)` of type `OsinLemma94CaseOneSameCellStatement`.  That
  statement is proved outright as `osinLemma94CaseOneSameCell` (`Estimating/OsinLemma94SameCellClosed`),
  which goes through the restricted form `enclosedSubdiagramLoopCutSuccLong` (relator words longer than
  one letter).  The unrestricted piece 03, which allows relator words of length one, has no known
  proof, and this waist does not need it.

The other closed ingredients are the ones V8 and V8Closures already use:
`sameCellPocketCellFreeValue`, `osinLemma94CaseOneWalk`, `osinLemma94CaseTwoInput`,
`cellPocketCopyCleanBothOrders`, `cellPocketWalkOuterOffSideSomeOrder`, `cellPocketWalkEuler`,
`GeodesicCollar.StripStep.geodesicCollarStatement_holds`, `pocketCellTransport`, `osinLoopCutSection`,
`osinCornerTwoGonSection` and `osinTwoGonDecompositionEulerSection`.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`: pieces 01 and 04–10 of the
  Greendlinger leaf give `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.

## Open residuals and the landed API next to them (for the piece agents)

* 01 `OsinLemma94ClassEndLoopsBudgetInput` (`Estimating/OsinLemma94ClassEndLoopsSide`).  Producer
  `osinLemma94ClassEndLoopsBudgetInput_of_joins` (`Estimating/OsinLemma94ClassJoins`), over
  `OsinLemma94BadJunctionInput` (← `osinLemma94BadJunctionInput_of_pieces`),
  `OsinLemma94ClassJoinsEndLoopsInput` and `OsinLemma94LongTransitionInput`
  (← `osinLemma94LongTransitionInput_of_pieces`).
* 04 `OsinLemma94ClassCaseGapSpanStatement` (`Estimating/OsinLemma94ClassPairShapes`).  No producer.
  Calibrations: `Estimating/OsinLemma94ClassGapSpanModel`, `Estimating/OsinLemma94ClassGapCollapseModel`
  (the collapse route does not exist), `osinLemma94ShortCaseOne_false` (`Estimating/OsinLemma94ShortCaseOne`).
* 05 `OsinTwoGonCleanCopySectionStatement` (`Estimating/OsinAppendixEulerTwoGonCopyRoute`).  Producer
  `osinTwoGonCleanCopySection_of_steps` (`Estimating/OsinAppendixEulerTwoGonCleanCopy`) over six
  `TwoGon…StepStatement`s.
* 06 `CellPocketOuterPinchStepSectionDistinctStatement` (`Estimating/OsinPocketCellPinchSectionDistinct`).
  No producer.  Landed steps: `CellPocketFaceSet.exists_cellPinchStepDistinct_of_isolatedTurn`
  (`Estimating/OsinPocketCellOuterPinchStep`), `CellPocketFaceSet.outerSpurThickening` and its lemmas
  (`Estimating/OsinPocketCellOuterSpur`), `CellPocketFaceSet.exists_simple_of_firstTurns`
  (`Estimating/OsinPocketCellGoodCorners`).
* 07 `CellPocketWalkProperArcsBelowSectionStatement` (`Estimating/OsinPocketMultipleEdgeCopyBelow`).
  Producer `CellPocketWalkProperArcsSectionStatement.toBelow`, whose premise has no producer.
* 08 `OsinSectionPocketFaceSetProperSectionStatement` (`Estimating/OsinPocketPinchSection`).  Producer
  `OsinSectionPocketFaceSetFirstTurnSectionStatement.toProper` (`Estimating/OsinPocketPinchFirstTurnAssembly`).
* 09 `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement` (`Estimating/OsinPocketTwoArcSection`).
  No producer.  Calibration: `Estimating/OsinPocketWholeSectionWrapModel`.
* 10 `PocketOuterPinchStepSectionStatement` (`Estimating/OsinPocketPinchOuterDispatch`).  No producer.
  Landed steps: `PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn`
  (`Estimating/OsinPocketOuterPinchChord`), `OuterPinchCorners.exists_outside_of_not_firstTurn` and
  `PocketFaceSet.exists_not_firstTurn` (`Estimating/OsinPocketOuterPinchCorners`), the corner options in
  `Estimating/OsinPocketOuterPinchCornerFix`, `PocketFaceSet.outerSpurThickening`
  (`Estimating/OsinPocketOuterSpur`), `PocketFaceSet.exists_simple_of_firstTurns`
  (`Estimating/OsinPocketGoodCornersSection`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.4, 9.7 and
4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from eight leaf residuals**: the V8 waist with the
same-cell pocket loop cut supplied by `sameCellPocketLoopCut` and the Case 1 same-cell branch supplied
by `osinLemma94CaseOneSameCell`, so the successor-form enclosed loop cut is not consumed. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwocopy : OsinTwoGonCleanCopySectionStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v})
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
      (osinMultipleEdgePocketRegionCopyBelowSection_of_pinchSectionOrderEuler
        cellPocketCopyCleanBothOrders cellPocketWalkOuterOffSideSomeOrder
        cellPocketWalkEuler
        (cellPocketPinchSectionDistinctStatement_of_outerPinchStep hcellStep) hproper)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection
      (osinTwoGonHoldsSection_of_cleanCopyEuler htwocopy osinTwoGonDecompositionEulerSection))
    (osinSectionPocketCutSection_of_residualsTwoArc
      (osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection hfaces hwhole)
      (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals
