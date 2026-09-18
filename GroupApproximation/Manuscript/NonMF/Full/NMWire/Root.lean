import GroupApproximation.Manuscript.NonMF.Full.NMWire.Waist
import GroupApproximation.Manuscript.NonMF.Full.NMWire.Step
import GroupApproximation.Manuscript.NonMF.Full.NMWire.CopyPocket
import GroupApproximation.Manuscript.NonMF.Full.NMWire.CopyCell
import GroupApproximation.Meta.AxiomGuard

/-!
# The two roots from exact conjunctions of live leaves

This module gives both roots, `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` and
`Full.TorsionFreeEndpoints.TorsionFreeEndpoints`, from two routes.

* **Route A**:
  * the kept-walk core (residual 10);
  * the corrected enclosed pocket and the short nearest pocket (binder 5).
* **Route B**:
  * the kept-walk core (residual 10);
  * the uncut rose statement (06) and residual 07 (binder 5).

Every other input is closed.  This module is routing only.  It certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.NMWire

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Route A to Osin's Lemma 4.4 at least-area diagrams.** -/
theorem nmWire_greendlinger_of_core_corrected_shortPocket
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v})
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (hshort : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  nmWire_greendlinger_of_copy_step (nmWire_copy_of_corrected_shortPocket hencl hshort)
    (nmWire_step_of_keptSubwalkCore hcore)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_greendlinger_of_core_corrected_shortPocket

/-- **Route A to the zero-parameter torsion-free endpoints.** -/
theorem nmWire_torsionFreeEndpoints_of_core_corrected_short
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0})
    (hencl : GroupApproximation.Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{0, 0, 0})
    (hshort : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire_greendlinger_of_core_corrected_shortPocket hcore hencl hshort)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_core_corrected_short

/-- **Route B to Osin's Lemma 4.4 at least-area diagrams**, with residual 07 left as a node. -/
theorem nmWire_greendlinger_of_core_uncut_proper
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v})
    (h06 : GreendlingerLeaf.Piece06.CellRoseUncutStatement.{u, w, v})
    (h07 : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  nmWire_greendlinger_of_copy_step (nmWire_copy_of_cellRoseUncut_proper h06 h07)
    (nmWire_step_of_keptSubwalkCore hcore)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_greendlinger_of_core_uncut_proper

/-- **Route B to the zero-parameter torsion-free endpoints**, with residual 07 taken from any one
of its three P07 leaves. -/
theorem nmWire_torsionFreeEndpoints_of_core_uncut_p07
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0})
    (h06 : GreendlingerLeaf.Piece06.CellRoseUncutStatement.{0, 0, 0})
    (h07 : GreendlingerLeaf.P07LakeExclusion.AllCellsShortLoopStatement.{0, 0, 0} ∨
      GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0} ∨
      GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire_greendlinger_of_core_uncut_proper hcore h06 (nmWire_proper_of_p07Leaf h07))

#audit_axioms GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_core_uncut_p07

end GroupApproximation.Full.NMWire
