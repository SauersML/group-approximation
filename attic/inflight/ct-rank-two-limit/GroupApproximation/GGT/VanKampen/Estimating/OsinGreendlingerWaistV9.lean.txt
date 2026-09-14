import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV8
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoins
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94LongTransitions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingTransitionsInput
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDecompositionEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The leaf-level Greendlinger waist, pushed further down

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4.  An additive recomposition of
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8` (`OsinGreendlingerWaistV8`):

* the budget of the class end loops from the class joins, `osinLemma94ClassEndLoopsBudgetInput_of_joins`
  (`OsinLemma94ClassJoins`), over the long transitions from the contact and cutting transitions
  (`osinLemma94LongTransitionInput_of_pieces`, with the cutting transitions proved,
  `osinLemma94CuttingTransitionInput`), the bad junctions from the cell junction value and the boundary
  junction budget (`osinLemma94BadJunctionInput_of_pieces`), the boundary junction budget from the
  backward junction count and the boundary value failure count
  (`osinLemma94BoundaryJunctionBudgetInput_of_pieces`), and the end loops of the class joins;
* the successor-form enclosed subdiagram is proved, `closedWalkEnclosedSubdiagramSucc`
  (`ClosedWalkEnclosedSubdiagramSuccAssembly`);
* the Euler equalities of the two-gon decomposition walk are proved, `osinTwoGonDecompositionEulerSection`
  (`OsinAppendixEulerTwoGonDecompositionEuler`).

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV9`: fourteen named leaf residual Props.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from fourteen leaf residuals**: the waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8` with the class end loop budget produced
from the class joins and their pieces, and the successor-form enclosed subdiagram and the two-gon
decomposition Euler equalities supplied by their proofs. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV9
    (hcontact : OsinLemma94ContactTransitionInput.{u, w, v})
    (hval : OsinLemma94CellJunctionValueInput.{u, w, v})
    (hback : OsinLemma94BackwardJunctionCountInput.{u, w, v})
    (hfail : OsinLemma94BoundaryValueFailureCountInput.{u, w, v})
    (hjoins : OsinLemma94ClassJoinsEndLoopsInput.{u, w, v})
    (hcut : SameCellPocketLoopCutStatement.{u, w, v})
    (hloop : EnclosedSubdiagramLoopCutSuccStatement.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (htwocopy : OsinTwoGonCleanCopySectionStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hwhole : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8
    (osinLemma94ClassEndLoopsBudgetInput_of_joins
      (osinLemma94LongTransitionInput_of_pieces hcontact osinLemma94CuttingTransitionInput)
      (osinLemma94BadJunctionInput_of_pieces hval
        (osinLemma94BoundaryJunctionBudgetInput_of_pieces hback hfail))
      hjoins)
    hcut hloop closedWalkEnclosedSubdiagramSucc hspan htwocopy
    osinTwoGonDecompositionEulerSection hcellStep hproper hfaces hwhole hstep

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV9
