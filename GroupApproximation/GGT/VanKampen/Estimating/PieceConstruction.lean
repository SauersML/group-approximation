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

/-- **The Piece construction from the ear statement alone.**  The
non-cancellation input is no longer a hypothesis: it is discharged by
`estimatingPieceNonCancellationStatement`, which reads Osin's `O52` certificate
off `Embedded.Contiguity` and turns it into the inequality using
`DiscDiagram.Reduced`.  So the only remaining input to the estimating Piece
construction is vk's planar ear statement.

**What a contiguity producer must now supply.**  `IsCandidate` is
correspondingly stronger: est's Lemma 65(a) construction, behind
`EstimatingSelectionConstructionStatement`, must supply the
`Embedded.Contiguity` fields `target_ne_source` and `o52Certificate` when it
builds a region, that is the stored-order split at the two cells, both cells
read forwards, the two arc alignments, and the connector identity along the
target arc and back along the right side. -/
theorem estimatingPieceConstruction_of_ear
    (hear : Embedded.FaceSetEarStatement.{u, w, v}) :
    EstimatingPieceConstructionStatement.{u, w, v} :=
  estimatingPieceConstruction_of_earStatement hear
    estimatingPieceNonCancellationStatement

/-- **The Piece construction, with no hypothesis.**  Every input is now a field
of the region itself: `pasting` gives the boundary-dart equation and
`o52Certificate` with `target_ne_source` gives the non-cancellation clause.
This closes `EstimatingPieceConstructionStatement` outright. -/
theorem estimatingPieceConstructionStatement :
    EstimatingPieceConstructionStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta scaffold hred
  refine ⟨{ equations := ?_ }⟩
  intro edge
  exact Embedded.cellPieceEquations_of_contiguity edge.candidate.contiguity
    edge.target_eq
    (estimatingPieceNonCancellationStatement D eps Delta
      scaffold.selected.family hred edge edge.target edge.target_eq)

/-- **The Piece construction from the region shelling statement.**  This is the
form to prefer over `estimatingPieceConstruction_of_ear`:
`GGT.VanKampen.RegionShellingStatement` is strictly weaker than
`Embedded.FaceSetEarStatement` -- it asks only that a selected face set admit a
shelling, not that an ear exist, that erasing it leave a single boundary cycle,
or that the ear face be unpinched -- and it is the same residue the Hull leaves
now sit on, so the paths unify on one open Prop instead of two. -/
theorem estimatingPieceConstruction_of_shelling
    (hshelling : RegionShellingStatement.{u, w, v}) :
    EstimatingPieceConstructionStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta scaffold hred
  refine ⟨{ equations := ?_ }⟩
  intro edge
  exact Embedded.cellPieceEquations_of_pasting edge.candidate.contiguity
    (faceSetWordHomotopy_of_regionShelling hshelling
      edge.candidate.contiguity.boundary)
    edge.target_eq
    (estimatingPieceNonCancellationStatement D eps Delta
      scaffold.selected.family hred edge edge.target edge.target_eq)

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
