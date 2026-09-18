import GroupApproximation.Manuscript.NonMF.Full.NMWire2.Census
import GroupApproximation.Manuscript.NonMF.Full.NMWire.Lobe
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual 10 from lobe removal, with the corrected enclosed pocket discharged

`NMWire.Lobe` combines lobe removal (the P10Rose route to residual 10) with the binder 5
alternatives `NMWire.nmWire_CopyLeaves`.  This module combines it with the binder 5 alternatives
after the discharge:

* `nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyLeaves` takes `nmWire2_CopyLeaves`, which
  has no `hencl` conjunct;
* `nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyResiduals` takes the residual alternatives
  `nmWire2_CopyResiduals`;
* `nmWire2_torsionFreeEndpoints_of_lobeRemoval_allCells` takes the all-cells refutation alone.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire2

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **The zero-parameter torsion-free endpoints from lobe removal and a residual binder 5
alternative.** -/
theorem nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyResiduals
    (hlobe : GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{0, 0, 0})
    (hcopy : nmWire2_CopyResiduals) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  NMWire.nmWire_torsionFreeEndpoints_of_copy_step (nmWire2_copy_of_copyResiduals hcopy)
    (NMWire.nmWire_step_of_lobeRemoval hlobe)

#audit_axioms
  GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyResiduals

/-- **The zero-parameter torsion-free endpoints from lobe removal and a binder 5 alternative,
`hencl` discharged.** -/
theorem nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyLeaves
    (hlobe : GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{0, 0, 0})
    (hcopy : nmWire2_CopyLeaves) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  NMWire.nmWire_torsionFreeEndpoints_of_lobeRemoval_copyLeaves hlobe
    (nmWire2_copyLeaves_iff.mp hcopy)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyLeaves

/-- **The zero-parameter torsion-free endpoints from lobe removal and the all-cells
refutation.** -/
theorem nmWire2_torsionFreeEndpoints_of_lobeRemoval_allCells
    (hlobe : GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{0, 0, 0})
    (hall :
      GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  nmWire2_torsionFreeEndpoints_of_lobeRemoval_copyResiduals hlobe (Or.inl hall)

#audit_axioms GroupApproximation.Full.NMWire2.nmWire2_torsionFreeEndpoints_of_lobeRemoval_allCells

end GroupApproximation.Full.NMWire2
