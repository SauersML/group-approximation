import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.CellStepBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseCut
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.GlFix01
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArc
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Route2
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyClean
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkOrder
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 5 from residual 06 (the cell pinch step) and residual 07 (the proper arcs)

Binder 5 comes from five inputs through
`osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler`.  Three of them are
closed: `cellPocketCopyCleanBothOrders`, `cellPocketWalkOuterOffSideSomeOrder` and
`cellPocketWalkEuler`.  The other two are open:

* The pinch below, obtained from residual 06.
* Residual 07, `CellPocketWalkProperArcsBelowSectionStatement`.

Residual 06 comes from `Piece06.CellRoseUncutStatement`.  The route goes through
`Piece06.cellRoseStep_of_uncut`, then `Piece06.proof_of_cellRoseStep` together with the closed
`Piece06.MonogonCorner.badCornerRefinement`, then the below form.

Residual 07 comes from any of three P07 leaves:

* `AllCellsShortLoopStatement`
* `CellPocketInnerTwoArcLongStatement`
* `LakeFillOutsideStatement`

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Residual 06, below form, from the uncut rose statement** (Osin, proof of Lemma 9.7(b)). -/
theorem nmWire_cellStepBelow_of_cellRoseUncut
    (h : GreendlingerLeaf.Piece06.CellRoseUncutStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} :=
  CellPocketOuterPinchStepSectionDistinctStatement.toBelow
    (GreendlingerLeaf.Piece06.proof_of_cellRoseStep
      (GreendlingerLeaf.Piece06.cellRoseStep_of_uncut h)
      GreendlingerLeaf.Piece06.MonogonCorner.badCornerRefinement)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_cellStepBelow_of_cellRoseUncut

/-- **Binder 5 from residual 06 (below form) and residual 07**, with the closed copy, order and
Euler inputs filled in. -/
theorem nmWire_copy_of_cellStepBelow_proper
    (h06 : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v})
    (h07 : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler
    cellPocketCopyCleanBothOrders cellPocketWalkOuterOffSideSomeOrder cellPocketWalkEuler
    (cellPocketPinchSectionDistinctBelowStatement_of_outerPinchStepBelow h06) h07

#audit_axioms GroupApproximation.Full.NMWire.nmWire_copy_of_cellStepBelow_proper

/-- **Binder 5 from the uncut rose statement and residual 07.** -/
theorem nmWire_copy_of_cellRoseUncut_proper
    (h06 : GreendlingerLeaf.Piece06.CellRoseUncutStatement.{u, w, v})
    (h07 : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  nmWire_copy_of_cellStepBelow_proper (nmWire_cellStepBelow_of_cellRoseUncut h06) h07

#audit_axioms GroupApproximation.Full.NMWire.nmWire_copy_of_cellRoseUncut_proper

/-- **Residual 07 from any one of its three P07 leaves.** -/
theorem nmWire_proper_of_p07Leaf
    (h : GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement.{u, w, v} ∨
      GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v} ∨
      GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  rcases h with hall | hlong | hfill
  · exact GreendlingerLeaf.P07LakeExclusion.glFix01_proof_of_allCells hall
  · exact GreendlingerLeaf.P07LakeExclusion.proof_of_innerTwoArcLong hlong
  · exact GreendlingerLeaf.P07LakeExclusion.proof_of_gaps' hfill

#audit_axioms GroupApproximation.Full.NMWire.nmWire_proper_of_p07Leaf

end GroupApproximation.Full.NMWire
