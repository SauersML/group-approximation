import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.EightResidualWaistBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The open-residual interface of the Greendlinger waist (Below form)

The Below waist `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`
(`GreendlingerLeaf/Common/EightResidualWaistBelow`) has eight binders, in the order
`hbudget, hspan, htwocopy, hcellStep, hproper, hfaces, hwhole, hstep`.  Three of them
(`htwocopy`, `hfaces`, `hwhole`, the residuals 05, 08 and 09) have hypothesis-free producers.  The
other five (residuals 01, 04, 06, 07 and 10) are still produced by region lanes.

This module only needs the waist module.  It defines

* `GreendlingerOpenResidualsBelowStatement`: the conjunction of the five open residuals;
* `ClosedTrioStatement`: the conjunction of the three closed residuals.  This is the interface of
  lane gl-assembly-01 (`AsmTrio.closedTrio`), which was not on disk when this lane was authored.  The
  producer `AsmWaist.closedTrio` (module `AsmWaist/Trio`) proves it from the three existing
  hypothesis-free theorems `Piece05.proof`, `P08ProperArc.proof` and `Piece09.proof`;

and proves the two reductions of the Greendlinger waist over them, with the closed trio still a
hypothesis:

* `relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow_of_closedTrio`: five unbundled
  binders plus the trio;
* `relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow_of_closedTrio`: the bundled
  form.

The unconditional-in-the-trio endpoints are in `AsmWaist/Endpoint`.

## Truth check

Nothing to check: the Below waist is already a proved reduction, and the conjunctions below split
its eight binders into two groups without changing any of them.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist

universe u w v

/-- **The five open residuals of the Below Greendlinger waist**: residual 01 (the class end-loop
budget), 04 (the class-case gap span), 06 (the outer-pinch cell step for distinct cells below the
inductive bound), 07 (proper arcs of the cell pocket walk below the bound) and 10 (the outer pinch
step of the section pocket). -/
def GreendlingerOpenResidualsBelowStatement : Prop :=
  OsinLemma94ClassEndLoopsBudgetInput.{u, w, v} ∧
    OsinLemma94ClassCaseGapSpanStatement.{u, w, v} ∧
      CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} ∧
        CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} ∧
          PocketOuterPinchStepSectionStatement.{u, w, v}

/-- **The three closed residuals of the Below Greendlinger waist** (residuals 05, 08 and 09): the
interface of lane gl-assembly-01, `AsmTrio.closedTrio`. -/
def ClosedTrioStatement : Prop :=
  OsinTwoGonCleanCopySectionStatement.{u, w, v} ∧
    OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} ∧
      OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v}

/-- **Osin's Lemma 4.4 at least-area diagrams from the five open residuals and the closed trio**:
the Below waist with its binders fed in the order `hbudget, hspan, htwocopy, hcellStep, hproper,
hfaces, hwhole, hstep`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow_of_closedTrio
    (htrio : ClosedTrioStatement.{u, w, v})
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v})
    (hcellStep : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v})
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} := by
  obtain ⟨htwocopy, hfaces, hwhole⟩ := htrio
  exact relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow
    hbudget hspan htwocopy hcellStep hproper hfaces hwhole hstep

/-- **Osin's Lemma 4.4 at least-area diagrams from the bundled open residuals and the closed
trio.** -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow_of_closedTrio
    (htrio : ClosedTrioStatement.{u, w, v})
    (h : GreendlingerOpenResidualsBelowStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} := by
  obtain ⟨hbudget, hspan, hcellStep, hproper, hstep⟩ := h
  exact relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow_of_closedTrio
    htrio hbudget hspan hcellStep hproper hstep

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow_of_closedTrio
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_openResidualsBelow_of_closedTrio
