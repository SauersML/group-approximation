import GroupApproximation.Manuscript.NonMF.Full.NMWire.Census
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.JunctionCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Residual 10 from lobe removal

This is the other Piece10 route to residual 10.  It starts from
`P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement` and reaches the step through
`Piece10.roseJunctionCore_proof_of_lobeRemoval`.  That route goes through the P10Rose stack, not
through GL06f, so it is kept apart from `NMWire.Census`.  It is combined here with the binder 5
alternatives `nmWire_CopyLeaves`.

This module is routing only.  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.NMWire

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **Residual 10 from lobe removal** (Osin, §9, proof of Lemma 9.7(b); `thm:hull`). -/
theorem nmWire_step_of_lobeRemoval
    (h : GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  GreendlingerLeaf.Piece10.roseJunctionCore_proof_of_lobeRemoval h

#audit_axioms GroupApproximation.Full.NMWire.nmWire_step_of_lobeRemoval

/-- **The zero-parameter torsion-free endpoints from lobe removal and a binder 5 alternative.** -/
theorem nmWire_torsionFreeEndpoints_of_lobeRemoval_copyLeaves
    (hlobe : GreendlingerLeaf.P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement.{0, 0, 0})
    (hcopy : nmWire_CopyLeaves) :
    GroupApproximation.Full.TorsionFreeEndpoints.TorsionFreeEndpoints :=
  nmWire_torsionFreeEndpoints_of_copy_step (nmWire_copy_of_copyLeaves hcopy)
    (nmWire_step_of_lobeRemoval hlobe)

#audit_axioms GroupApproximation.Full.NMWire.nmWire_torsionFreeEndpoints_of_lobeRemoval_copyLeaves

end GroupApproximation.Full.NMWire
