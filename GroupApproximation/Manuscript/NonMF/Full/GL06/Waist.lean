import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInductionBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSectionTwoThreshold
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassEndLoopsSide
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellFactorInput
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketCellFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketLoopCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCasesTwoThreshold
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOneRun
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellClosed
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseTwo
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairShapes
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerParts
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGonSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonCopyRoute
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDecompositionEuler
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoArcSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSection
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.Proof
import GroupApproximation.Manuscript.NonMF.Full.GL02.GapSpan
import GroupApproximation.Manuscript.NonMF.Full.GL06d.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06: the Below Greendlinger waist with the remaining residuals as hypotheses

Osin, arXiv:math/0411039v3, Lemma 4.4, through the induction of §9 (Lemma 9.4 and Lemma 9.7(b)) at
least-area diagrams below the inductive bound.  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem).

The term is the Below waist `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow`
(`Estimating/OsinAppendixSectionInductionBelow`), fed as in the foreign
`GreendlingerLeaf/P06Bypass/WaistBinderFive` (which is not imported: it imports the WIP-tainted
`AsmTrio/ClosedTrio`), with two closed residuals supplied here:

* residual 04, the class-case gap span: `Full.GL02.gapSpan`;
* residual 08, the proper face-set section: `GreendlingerLeaf.P08ProperArc.proof`.

The remaining residuals are hypotheses, discharged in `Full/GL06/Assembly`:

* `hbudget`: residual 01, `OsinLemma94ClassEndLoopsBudgetInput`;
* `htwocopy`: residual 05, `OsinTwoGonCleanCopySectionStatement`;
* `hwhole`: residual 09, `OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement`;
* `hcopy`: binder 5 below the bound, `OsinMultipleEdgePocketRegionCopyBelowSectionStatement`;
* `hstep`: residual 10, `PocketOuterPinchStepSectionStatement`.

`outerPinchStep_of_cases` splits residual 10 into the rose case (`P10ChordLift.RoseStepStatement`)
and its complement (`Full.GL06d.NonRoseStepStatement`), by excluded middle on
`P10ChordLift.AllNonFirstTurnsCrossed`.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Residual 10 from its rose case and its non-rose case** (Osin, §9, proof of Lemma 9.7(b);
`thm:hull`).  Both cases have the same hypotheses up to the rose predicate; the thresholds are the
larger of the two. -/
theorem outerPinchStep_of_cases
    (hnon : GroupApproximation.Full.GL06d.NonRoseStepStatement.{u, w, v})
    (hrose : GreendlingerLeaf.P10ChordLift.RoseStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₁, he₁⟩ := hnon D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₂, he₂⟩ := hrose D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e₁ e₂, fun eps heps => ?_⟩
  obtain ⟨r₁, hr₁, hR₁⟩ := he₁ eps (le_of_max_le_left heps)
  obtain ⟨r₂, -, hR₂⟩ := he₂ eps (le_of_max_le_right heps)
  refine ⟨max r₁ r₂, lt_max_of_lt_left hr₁, fun rho hrho W hW X lo hi hlea hlabel K hclosed
    hfirst hsource htarget hpinched => ?_⟩
  rcases Classical.em (GreendlingerLeaf.P10ChordLift.AllNonFirstTurnsCrossed K) with hall | hall
  · exact hR₂ rho (le_of_max_le_right hrho) W hW X lo hi hlea hlabel K hclosed hfirst hsource
      htarget hpinched hall
  · exact hR₁ rho (le_of_max_le_left hrho) W hW X lo hi hlea hlabel K hclosed hfirst hsource
      htarget hpinched hall

/-- **Osin's Lemma 4.4 at least-area diagrams from the remaining residuals** (Osin, Lemma 4.4 via
Lemma 9.4 and Lemma 9.7(b); `thm:hull`).  The Below waist with residual 04 supplied by
`Full.GL02.gapSpan` and residual 08 by `P08ProperArc.proof`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (htwocopy : OsinTwoGonCleanCopySectionStatement.{u, w, v})
    (hwhole : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v})
    (hcopy : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v})
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
        osinLemma94CaseTwoInput GroupApproximation.Full.GL02.gapSpan.{u, w, v}))
    (osinMultipleEdgeCutBelowSection_of_copyPieces hcopy
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection
      (osinTwoGonHoldsSection_of_cleanCopyEuler htwocopy osinTwoGonDecompositionEulerSection))
    (osinSectionPocketCutSection_of_residualsTwoArc
      (osinSectionPocketFaceSetTwoArcSection_of_proper_of_wholeSection
        GreendlingerLeaf.P08ProperArc.proof.{u, w, v} hwhole)
      (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.Full.GL06

#audit_axioms GroupApproximation.Full.GL06.outerPinchStep_of_cases
#audit_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
