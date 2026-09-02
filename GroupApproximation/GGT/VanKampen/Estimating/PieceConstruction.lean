import GroupApproximation.GGT.VanKampen.Estimating.PieceCore
import GroupApproximation.GGT.VanKampen.Estimating.Assembly

/-!
# Closing the Piece construction along a scaffold

`Estimating/PieceCore.lean` proves the two-arc certificate at one embedded
region from vk's `Embedded.FaceSetEarStatement` and the single named Prop
`EstimatingPieceNonCancellationStatement`.  This module specializes that
constructor along an estimating scaffold, which closes
`EstimatingPieceConstructionStatement` with those two inputs and nothing else.

The target index and its equation are not inputs: `Embedded.InteriorEdge` is by
definition a selected candidate together with a relator-cell index and the
proof that the candidate's contiguity targets it, so the outer-boundary case
never reaches this construction.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-- **The Piece construction from the planar ear statement and the local
inequality.**  These are the only two hypotheses. -/
theorem estimatingPieceConstruction_of_earStatement
    (hear : Embedded.FaceSetEarStatement.{u, w, v})
    (hne : EstimatingPieceNonCancellationStatement.{u, w, v}) :
    EstimatingPieceConstructionStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta scaffold hred
  refine ⟨{ equations := ?_ }⟩
  intro edge
  exact Embedded.cellPieceEquations_of_earStatement hear
    edge.candidate.contiguity edge.target_eq
    (hne D eps Delta scaffold.selected.family hred edge edge.target
      edge.target_eq)

/-- Model test at the empty relator family: the target structure of the
construction statement is inhabited, because an interior edge carries a
relator-cell index and there is none. -/
theorem cellPieceData_of_rCellCount_zero
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hzero : Delta.rCellCount = 0) :
    Nonempty (CellPieceData D eps Delta scaffold) := by
  refine ⟨{ equations := ?_ }⟩
  intro edge
  exact absurd edge.target.isLt (by omega)

end VanKampen
end GGT
end GroupApproximation
