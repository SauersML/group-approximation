import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Trio
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist over the five open residuals (Below form)

Lane gl-assembly-02 endpoints.  With the closed trio `AsmWaist.closedTrio` (residuals 05, 08, 09)
discharged, the Below waist `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`
depends only on the five open residuals:

* `relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow`: from the bundled
  `GreendlingerOpenResidualsBelowStatement`;
* `relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow`: from the five residuals as
  separate binders, in the order `hbudget, hspan, hcellStep, hproper, hstep` (the order of the
  eight-binder waist with `htwocopy`, `hfaces` and `hwhole` removed).

Lane gl-assembly-04 applies the five-binder form to the hypothesis-free region endpoints.  These are
Statement-hypothesis reductions (interfaces), not census endpoints.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from the five open residuals of the Below waist**,
given as separate binders; residuals 05, 08 and 09 are supplied by `closedTrio`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow_of_closedTrio
    closedTrio.{u, w, v} hbudget hspan hcellStep hproper hstep

/-- **Osin's Lemma 4.4 at least-area diagrams from the bundled open residuals of the Below
waist.** -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow
    (h : GreendlingerOpenResidualsBelowStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow_of_closedTrio
    closedTrio.{u, w, v} h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow
