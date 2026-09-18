import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Rotation
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through a cell side doubling

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellSideStepStatement`.

The cell side doubling carries the family (`transport`, crossings through `embed`, since no arc
of the family contains the doubled dart and no region contains the face `f`), and carries `Φ'_M`
at every component (`phiTransportAt`: the collapsed rotation agrees along `embed` up to the detour
through `some none`, and face-class paths to relator cells are named back).  A clean two-gon is
then carried by `hasCleanTwoGon_of_transport`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide

universe u w v

/-- **A clean two-gon through a cell side doubling.** -/
theorem proof : TwoGonCellSideStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S f j hlen hf havoid h
  exact hasCleanTwoGon_of_transport hlea (transport S f j hlen hf havoid)
    (fun a₀ => phiTransportAt S f j hlen hf havoid a₀) h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.proof
