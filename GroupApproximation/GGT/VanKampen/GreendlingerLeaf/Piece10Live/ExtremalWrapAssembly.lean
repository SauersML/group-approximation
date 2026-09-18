import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapPinch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 4.4 at least-area diagrams from the no-wrap extremal core

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12a.

`P06Bypass.Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow` feeds residual 10
(`hstep : PocketOuterPinchStepSectionStatement`) only through
`osinSectionPocketCutSection_of_residualsTwoArc … (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep
hstep) …`.  This module copies that waist term with the no-wrap pinch
(`ExtremalWrapPinch`) in that slot, then copies `AssemblyResidual.relativeGreendlinger_of_residuals`
with residual 10 given by the no-wrap extremal core.

* `relativeGreendlinger_of_binderFiveBelowNoWrap` (proved): the waist with the no-wrap step.
* `relativeGreendlinger_of_residualsNoWrap` (proved): from `P07InnerPocket.PocketFourPieceOffStatement`
  and `RoseExtremalCoreNoWrapStatement`.
* `relativeGreendlinger_of_contigResidualNoWrap` (proved): from the four-piece-off residual and
  `RoseExtremalContigResidualNoWrapStatement`.

## Truth check

Nothing to check: proved terms with one subterm replaced by its no-wrap form.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

/-- **The Below waist with binder 5 and the no-wrap step**: the term of
`P06Bypass.Waist.relativeGreendlingerQuasiGeodesicLeastArea_of_binderFiveBelow`, with the section
pocket cut built from the no-wrap pinch. -/
theorem relativeGreendlinger_of_binderFiveBelowNoWrap
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hcopy : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionNoWrapStatement.{u, w, v}) :
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
    (osinSectionPocketCutSection_of_residualsTwoArcNoWrap
      (osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection hfaces hwhole)
      (pinchNoWrap_of_stepNoWrap hstep)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

/-- **Osin's Lemma 4.4 at least-area diagrams from the four-piece-off residual and the no-wrap
extremal core**: `AssemblyResidual.relativeGreendlinger_of_residuals` with residual 10 through the
no-wrap chain. -/
theorem relativeGreendlinger_of_residualsNoWrap
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hcore : RoseExtremalCoreNoWrapStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlinger_of_binderFiveBelowNoWrap Piece01.proof.{u, w, v} Piece04.proof.{u, w, v}
    (P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (P06Bypass.refutedBelowSection_of_innerPocketEnclosed
        (P07InnerPocket.innerPocketEnclosed_of_fourPieceOff hoff)))
    (stepNoWrap_of_extremalCoreNoWrap hcore)

/-- **Osin's Lemma 4.4 at least-area diagrams from the four-piece-off residual and the no-wrap
residual contiguity clauses.** -/
theorem relativeGreendlinger_of_contigResidualNoWrap
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hres : RoseExtremalContigResidualNoWrapStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlinger_of_residualsNoWrap hoff (extremalCoreNoWrap_of_contigResidualNoWrap hres)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.relativeGreendlinger_of_binderFiveBelowNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.relativeGreendlinger_of_residualsNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.relativeGreendlinger_of_contigResidualNoWrap
