import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerWaistV8
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDecompositionEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The V8 Greendlinger waist with two leaves closed

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4.  An additive recomposition of
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8` (`OsinGreendlingerWaistV8`) that only applies
closures, so every change removes a leaf and none is added:

* the successor-form enclosed subdiagram is proved, `closedWalkEnclosedSubdiagramSucc`
  (`ClosedWalkEnclosedSubdiagramSuccAssembly`);
* the Euler equalities of the two-gon decomposition walk are proved,
  `osinTwoGonDecompositionEulerSection` (`OsinAppendixEulerTwoGonDecompositionEuler`).

* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures`: ten named leaf residual Props, the
  leaves of V8 less the two closed ones.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemmas 9.7 and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from ten leaf residuals**: the waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8` with the successor-form enclosed subdiagram
and the two-gon decomposition Euler equalities supplied by their proofs. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
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
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8 hbudget hcut hloop
    closedWalkEnclosedSubdiagramSucc hspan htwocopy osinTwoGonDecompositionEulerSection hcellStep hproper
    hfaces hwhole hstep

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures
