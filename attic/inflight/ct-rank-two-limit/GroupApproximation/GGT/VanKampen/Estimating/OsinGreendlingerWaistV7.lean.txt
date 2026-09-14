import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV6
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSpurEnclosureProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkNoninterleavingJoints
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonSpanOfCopyClean
import GroupApproximation.Meta.AxiomGuard

/-!
# The leaf-level Greendlinger waist, recomposed

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4.  An additive recomposition of
the live waist `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5` at leaf level, with the
reductions of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV6` and three changes:

* the spur enclosure of Case 1 is proved, `osinLemma94CaseOneSpurEnclosure`
  (`OsinLemma94SameCellSpurEnclosureProof`);
* the non-interleaving of the cell pocket walks is proved, `cellPocketWalkNoninterleaving`
  (`OsinPocketCellWalkNoninterleavingJoints`);
* C6′ at section level comes from the edge conditions and the Euler equalities of the decomposition
  walk, `osinTwoGonHoldsSection_of_copyCleanEuler` (`OsinAppendixEulerTwoGonSpanOfCopyClean`), which
  needs no following cycle and covers pinch-type touches, instead of the Euler walk and gap inputs of V6.

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV7`: thirteen named leaf residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from thirteen leaf residuals**: the live waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5` with its residuals produced by the
reductions on origin, the spur enclosure and the non-interleaving of the cell pocket walks supplied by
their proofs, and C6′ from the edge conditions and the decomposition Euler equalities. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV7
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hvalue : SameCellPocketCellFreeValueStatement.{u, w, v})
    (hcut : SameCellPocketLoopCutStatement.{u, w, v})
    (hloop : EnclosedSubdiagramLoopCutSuccStatement.{u, w, v})
    (hsub : ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwoclean : OsinTwoGonCopyCleanSectionStatement.{u, w, v})
    (htwoeuler : OsinTwoGonDecompositionEulerSectionStatement.{u, w, v})
    (hcount : NoninterleavingVertexCountStatement.{v})
    (hcellStep : CellPocketOuterPinchStepSectionStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV5
    (osinLemma94ClassEndLoopsInput_of_budget hbudget)
    (osinLemma94SameCellPocketInput_of_loopCut hvalue hcut)
    (osinLemma94CaseOneRCell_of_noSpurPockets
      (osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSucc hloop)
      (osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSucc hloop)
      (osinLemma94CaseOneRCellSpur_of_enclosure hloop hsub osinLemma94CaseOneSpurEnclosure))
    hspan
    (osinTwoGonHoldsSection_of_copyCleanEuler htwoclean htwoeuler)
    (cellPocketWalkEuler_of_noninterleaving hcount cellPocketWalkNoninterleaving)
    (cellPocketPinchSectionStatement_of_outerPinchStep hcellStep)
    hproper hfaces
    (pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep hstep)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV7
