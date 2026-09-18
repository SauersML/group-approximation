import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.Rotation
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through an outer cell doubling

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterCellStepStatement`.

Mathematical proof.  The outer cell doubling along `w_j` carries every region `r` with
`faceOf (alpha w_j) ∉ r` to its thickened copy, with the same crossings through `embed`
(`transport`, `P05OuterCell/Crossing.lean`).  At every component it carries `Φ'_M`
(`phiTransportAt`, `P05OuterCell/Rotation.lean`): the collapsed face rotation agrees along `embed`
up to the detour through the new dart `some none`, the doubled dart `w_j` is not a crossing dart,
and face-class paths to relator cells are named back.  A clean two-gon of a least-area diagram is
then carried by `hasCleanTwoGon_of_transport` (`P05OuterCell/TwoGon.lean`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

universe u w v

/-- **A clean two-gon through an outer cell doubling.** -/
theorem proof : TwoGonOuterCellStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S j hlen havoid h
  exact hasCleanTwoGon_of_transport hlea (transport S j hlen havoid)
    (fun a₀ => phiTransportAt S j hlen havoid a₀) h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.proof
