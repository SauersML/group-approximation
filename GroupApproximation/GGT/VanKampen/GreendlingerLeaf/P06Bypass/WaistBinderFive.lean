import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.EightResidualWaistBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmTrio.ClosedTrio
import GroupApproximation.Meta.AxiomGuard

/-!
# The Below Greendlinger waist with binder 5 as a binder (lane gl-p06-03, first endpoint)

`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`
(`GreendlingerLeaf/Common/EightResidualWaistBelow`, :33) feeds binder 5,
`OsinMultipleEdgePocketRegionCopyBelowSectionStatement`, with the pinch term
`osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler … hcellStep hproper`.
Residuals 06 (`hcellStep`) and 07 (`hproper`) enter the waist only through that term.  This module
copies the term of the eight-residual waist with binder 5 as a hypothesis `hcopy`, and takes
residuals 05, 08 and 09 (`htwocopy`, `hfaces`, `hwhole`) from `AsmTrio.closedTrio`, exactly as
`AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow_of_closedTrio` does.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow`: residual 01 (`hbudget`), residual
  04 (`hspan`), binder 5 below the bound (`hcopy`) and residual 10 (`hstep`) give
  `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`.

## Truth check

Nothing to check: this is the proved eight-residual term with one subterm abstracted.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from residuals 01, 04, 10 and binder 5 below the
inductive bound**: the eight-residual Below waist with the pinch subterm replaced by `hcopy` and the
closed trio supplied by `AsmTrio.closedTrio`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hcopy : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} := by
  obtain ⟨htwocopy, hfaces, hwhole⟩ := AsmTrio.closedTrio.{u, w, v}
  exact relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow
    (osinLemma94Section_of_classCountTwoThreshold
      (osinLemma94ClassCountInput_of_endLoops (osinLemma94ClassEndLoopsInput_of_budget hbudget)
        (osinLemma94SameCellFactorInput_of_scan
          (osinLemma94SameCellScanInput_of_pocket
            (osinLemma94SameCellPocketInput_of_loopCut sameCellPocketCellFreeValue
              sameCellPocketLoopCut))))
      (osinLemma94ClassCasesTwoThreshold_of_residuals
        (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk osinLemma94CaseOneSameCell)
        osinLemma94CaseTwoInput hspan))
    (osinMultipleEdgeCutBelowSection_of_copyPieces hcopy
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection
      (osinTwoGonHoldsSection_of_cleanCopyEuler htwocopy osinTwoGonDecompositionEulerSection))
    (osinSectionPocketCutSection_of_residualsTwoArc
      (osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection hfaces hwhole)
      (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow
