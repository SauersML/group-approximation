import GroupApproximation.Manuscript.NonMF.Full.GL06.Waist
import GroupApproximation.Manuscript.NonMF.Full.GL06d.NonRose
import GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction
import GroupApproximation.Manuscript.NonMF.Full.GL03D.KeptWalk
import GroupApproximation.Manuscript.NonMF.Full.GL03D.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual 10 (the outer pinch step) from the Piece10 leaves

`GL06.outerPinchStep_of_cases` splits residual 10 into two cases.  The non-rose case is closed by
`GL06d.nonRoseStep`.  The rose case `GL06f.RoseStepStatement` comes from the sub-arc region move
through `GL06f.rose_of_regionMoveSubArc`.  The region move comes in turn from the kept sub-walk
(`GL03D.roseRegionMoveSubArc_of_keptSubwalk`), or from its core
(`GL03D.gl03dKept_roseRegionMoveSubArc_of_core`).

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Residual 10 from the sub-arc region move** (Osin, §9, proof of Lemma 9.7(b); `thm:hull`).
The non-rose case is `GL06d.nonRoseStep`. -/
theorem nmWire_step_of_roseRegionMoveSubArc
    (h : GroupApproximation.Full.GL06f.RoseRegionMoveSubArcStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  GroupApproximation.Full.GL06.outerPinchStep_of_cases GroupApproximation.Full.GL06d.nonRoseStep
    (GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc h)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_step_of_roseRegionMoveSubArc

/-- **Residual 10 from the kept sub-walk statement.** -/
theorem nmWire_step_of_keptSubwalk
    (h : GroupApproximation.Full.GL03D.KeptSubwalkStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  nmWire_step_of_roseRegionMoveSubArc
    (GroupApproximation.Full.GL03D.roseRegionMoveSubArc_of_keptSubwalk h)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_step_of_keptSubwalk

/-- **Residual 10 from the kept-walk core** `GL03DKept.gl03dKept_KeptSubwalkCoreStatement`. -/
theorem nmWire_step_of_keptSubwalkCore
    (h : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  nmWire_step_of_roseRegionMoveSubArc
    (GroupApproximation.Full.GL03D.gl03dKept_roseRegionMoveSubArc_of_core h)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_step_of_keptSubwalkCore

end GroupApproximation.Full.NMWire
