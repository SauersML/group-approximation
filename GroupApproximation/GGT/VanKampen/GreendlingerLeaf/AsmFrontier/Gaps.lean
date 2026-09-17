import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.PocketTurns
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.FullWord
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefineAssemble
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Frontier reductions for residuals 04, 06 and 07 of the Below waist

Lane gl-assembly-03, first module.  Each residual of the Below waist
(`GreendlingerLeaf/Common/EightResidualWaistBelow`) handled here is reduced to the open
region-level Statements that are still in flight:

* `gapSpan_of_rotationTurns` (residual 04, `hspan`): from
  `Piece04.ClassPocketRotationTurnStatement`, through `Piece04.rCell_of_classPocketRotationTurns`
  (`Piece04/PocketTurns`) and `Piece04.proof_of_gapSpanResidual` (`Piece04/Reduction`).  The second
  conjunct of `Piece04.GapSpanResidualStatement` is the hypothesis-free
  `Piece04.fullWordDiffKind` (`Piece04/FullWord`), so the rCell-to-gapSpan link is not a gap.
* `cellStepBelow_of_monogonCorner_lakes` (residual 06, `hcellStep`): from
  `Piece06.CornerRefine.MonogonCornerStatement` and `Piece06.CellRoseUncutLakesBelowStatement`,
  through `Piece06.CornerRefine.badCornerRefinement_of_monogonCorner` and
  `Piece06.proof_of_below_gaps`.  The lane names the first Statement `Piece06.MonogonCornerStatement`;
  its declaration lives in the namespace `Piece06.CornerRefine` (`Piece06/CornerRefine`).
* `properArcsBelow_of_innerTwoArcLong` (residual 07, `hproper`): from
  `P07LakeExclusion.CellPocketInnerTwoArcLongStatement`, through
  `P07LakeExclusion.proof_of_innerTwoArcLong`.

None of the modules `Piece04/Proof`, `Piece04/Residual`, `Piece06/Proof`, `Piece07/Proof` or
`GreendlingerLeaf/Assembly` is imported.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

universe u w v

/-- **Residual 04 from the rotation turns of a class pocket.**  The rCell half of
`Piece04.GapSpanResidualStatement` is `Piece04.rCell_of_classPocketRotationTurns`; the full-word
half is the hypothesis-free `Piece04.fullWordDiffKind`. -/
theorem gapSpan_of_rotationTurns
    (hrot : Piece04.ClassPocketRotationTurnStatement.{u, w, v}) :
    OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  Piece04.proof_of_gapSpanResidual
    (And.intro (Piece04.rCell_of_classPocketRotationTurns hrot) Piece04.fullWordDiffKind.{u, w, v})

/-- **Residual 06 from the monogon corner and the uncut lakes below.**  The bad-corner refinement
comes from the monogon corner; the Below cell step comes from the lakes and that refinement. -/
theorem cellStepBelow_of_monogonCorner_lakes
    (hmono : Piece06.CornerRefine.MonogonCornerStatement.{u, w, v})
    (hlakes : Piece06.CellRoseUncutLakesBelowStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} :=
  Piece06.proof_of_below_gaps hlakes
    (Piece06.CornerRefine.badCornerRefinement_of_monogonCorner hmono)

/-- **Residual 07 from the long inner two-arc Statement.** -/
theorem properArcsBelow_of_innerTwoArcLong
    (hinner : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  P07LakeExclusion.proof_of_innerTwoArcLong hinner

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.gapSpan_of_rotationTurns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.cellStepBelow_of_monogonCorner_lakes
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.properArcsBelow_of_innerTwoArcLong
