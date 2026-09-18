import GroupApproximation.Manuscript.NonMF.Full.NMWire2.Copy
import GroupApproximation.Manuscript.NonMF.Full.NMWire.Root
import GroupApproximation.Meta.AxiomGuard

/-!
# The two NM roots with the corrected enclosed pocket discharged

The roots are `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` and
`Full.TorsionFreeEndpoints.TorsionFreeEndpoints`.

* `nmWire2_greendlinger_of_core_shortPocket` and `nmWire2_torsionFreeEndpoints_of_core_short`:
  Route A of `NMWire.Root` with `hencl` discharged by the proved
  `GL03BPinch.innerPocketEnclosedTwoArcCorrected`.  The inputs left are the kept-walk core and
  the short nearest pocket.
* `nmWire2_greendlinger_of_step_allCells`, `nmWire2_greendlinger_of_core_allCells` and
  `nmWire2_torsionFreeEndpoints_of_core_allCells`: the same route with the short nearest pocket
  replaced by the weaker all-cells refutation
  `GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`.

Route B of `NMWire.Root` never took `hencl`, so nothing changes there.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire2

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **Route A to Osin's Lemma 4.4 at least-area diagrams, `hencl` discharged.** -/
theorem nmWire2_greendlinger_of_core_shortPocket
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v})
    (hshort : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  GroupApproximation.Full.NMWire.nmWire_greendlinger_of_core_corrected_shortPocket hcore
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected hshort

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_greendlinger_of_core_shortPocket

/-- **Route A to the zero-parameter torsion-free endpoints, `hencl` discharged.** -/
theorem nmWire2_torsionFreeEndpoints_of_core_short
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0})
    (hshort : GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_core_corrected_short hcore
    GroupApproximation.Full.GL03BPinch.innerPocketEnclosedTwoArcCorrected.{0, 0, 0} hshort

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_core_short

/-- **Osin's Lemma 4.4 at least-area diagrams from residual 10 and the all-cells refutation.** -/
theorem nmWire2_greendlinger_of_step_allCells
    (hstep : PocketOuterPinchStepSectionStatement.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  GroupApproximation.Full.NMWire.nmWire_greendlinger_of_copy_step (nmWire2_copy_of_allCells hall)
    hstep

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_greendlinger_of_step_allCells

/-- **Osin's Lemma 4.4 at least-area diagrams from the kept-walk core and the all-cells
refutation.** -/
theorem nmWire2_greendlinger_of_core_allCells
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  nmWire2_greendlinger_of_step_allCells
    (GroupApproximation.Full.NMWire.nmWire_step_of_keptSubwalkCore hcore) hall

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_greendlinger_of_core_allCells

/-- **The zero-parameter torsion-free endpoints from residual 10 and the all-cells
refutation.** -/
theorem nmWire2_torsionFreeEndpoints_of_step_allCells
    (hstep : PocketOuterPinchStepSectionStatement.{0, 0, 0})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire2_greendlinger_of_step_allCells hstep hall)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_step_allCells

/-- **The zero-parameter torsion-free endpoints from the kept-walk core and the all-cells
refutation.** -/
theorem nmWire2_torsionFreeEndpoints_of_core_allCells
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  GroupApproximation.Full.TorsionFreeEndpoints.torsionFreeEndpoints_of_greendlinger
    (nmWire2_greendlinger_of_core_allCells hcore hall)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_core_allCells

end GroupApproximation.Full.NMWire2
