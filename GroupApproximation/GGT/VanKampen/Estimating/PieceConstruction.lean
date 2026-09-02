import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.GGT.VanKampen.FaceSetPeelProducer

/-!
# The Piece construction from one planar statement and one local inequality

`EstimatingPieceConstructionStatement` asks for a `CellPieceEquations`
certificate at every selected interior edge.  That structure has exactly three
fields, and this module accounts for all three.

* `target` and `target_eq` are free: `Embedded.InteriorEdge` is by definition a
  selected candidate *together with* a relator-cell index and the proof that the
  candidate's contiguity targets it.  So the outer-boundary case never reaches
  this construction.
* `arcs_value` is the boundary-dart count.  Writing the face-set boundary cycle
  in its stored decomposition
  `sourceArc.reverse ++ rightSide ++ targetBoundary ++ leftSide`, the equation
  `target = right⁻¹ * source * left⁻¹` is exactly the statement that the cycle
  has trivial value, which is what a complete face-deletion schedule produces.
  `Contiguity.targetBoundary_value_of_pasting` performs that conversion and
  `FaceSetBoundaryPeeling.to_homotopy` supplies the schedule, so the only input
  is vk's `Embedded.FaceSetEarStatement`: every single-cycle `G`-region has an
  ear.  Nothing else in the peel is open.
* `whole_ne` is the non-cancellation inequality.  It is the *whole* content of
  `Embedded.ReducedCellPieceBridge`: the bridge's other four fields are a free
  repackaging, since `sourceWord` and `targetWord` may be taken to be the arc
  words themselves and `connector` is pinned by `connector_value_eq`.  So the
  bridge is not a smaller input than the inequality, and this module names the
  inequality directly as `EstimatingPieceNonCancellationStatement`.

**What remains, exactly.**  `estimatingPieceConstruction_of_earStatement` proves
`EstimatingPieceConstructionStatement` from vk's landed
`Embedded.FaceSetEarStatement` together with the single new Prop
`EstimatingPieceNonCancellationStatement`.  No other hypothesis is used.

**Why the new Prop is not a consequence of `Delta.Reduced` alone.**
`Embedded.InteriorEdge` does not require the source cell to differ from the
target cell, and `DiscDiagram.Reduced` only constrains *pairs* of relator cells
occurring in the stored order.  `reduced_of_rCellCount_le_one` shows every
diagram with at most one relator cell is reduced, and
`interiorEdge_source_eq_target_of_rCellCount_one` shows that at exactly one
relator cell every interior edge has `source = target`.  So at one cell the
hypothesis `Delta.Reduced` is vacuous while the inequality is not, and any
producer of `EstimatingPieceNonCancellationStatement` must either rule out
self-contiguous candidates or derive the inequality from something other than
`Delta.Reduced`.  This is recorded as a model test, not as a refutation: it
shows where the remaining content sits.

Model tests: `cellPieceData_of_rCellCount_zero` inhabits the target structure of
the construction statement at a diagram with no relator cells, and
`estimatingPieceNonCancellation_holds_of_rCellCount_zero` inhabits the body of
the new Prop there.  `estimatingPieceNonCancellation_of_reducedBridges` grounds
the new Prop in the landed `Embedded.ReducedCellPieceBridge` route.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-! ## The single remaining local input -/

/-- **The one local inequality still missing from the Piece construction.**
For a reduced diagram, no selected interior candidate has its target relator
carrier equal to the source relator rotated and conjugated by the region's
short right side.  This is the `whole_ne` field of `CellPieceEquations` and
nothing more; the other two fields are proved in this module. -/
def EstimatingPieceNonCancellationStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta),
    Delta.Reduced →
    ∀ (edge : Embedded.InteriorEdge scaffold.selected.family)
      (target : Fin Delta.rCellCount)
      (htarget : edge.candidate.contiguity.target = some target),
      GGT.RelLetter.listVal
          (edge.candidate.contiguity.targetInverseCarrier target htarget) ≠
        (GGT.RelLetter.listVal (Embedded.dartWord Delta
            edge.candidate.contiguity.rightSide))⁻¹ *
          GGT.RelLetter.listVal (Embedded.dartWord Delta
            edge.candidate.contiguity.sourceArc.rotated) *
          GGT.RelLetter.listVal (Embedded.dartWord Delta
            edge.candidate.contiguity.rightSide)

/-- The landed reduced-bridge route supplies the new Prop.  The bridge stores
the same inequality after the target index is identified, so this is the exact
sense in which the new Prop is not larger than the bridge family. -/
theorem estimatingPieceNonCancellation_of_reducedBridges
    (hbridge : ∀ {G : Type u} [Group G] {Lambda : Type w}
      (D : GGT.RelGenSet G Lambda) (eps : ℕ)
      {W : Set (List (GGT.RelLetter G Lambda))}
      (Delta : DiscDiagram.{u, w, v} W)
      (scaffold : EstimatingScaffold D eps Delta),
      Delta.Reduced →
      ∀ edge : Embedded.InteriorEdge scaffold.selected.family,
        Nonempty (Embedded.ReducedCellPieceBridge edge.candidate.contiguity)) :
    EstimatingPieceNonCancellationStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta scaffold hred edge target htarget
  obtain ⟨bridge⟩ := hbridge D eps Delta scaffold hred edge
  have hsome : some bridge.target = some target :=
    bridge.target_eq.symm.trans htarget
  have hidx : bridge.target = target := Option.some.inj hsome
  subst hidx
  exact bridge.whole_ne hred

/-! ## The Piece construction -/

/-- **The Piece construction from the planar ear statement and the local
inequality.**  The target index and its equation come from the interior edge
itself, the boundary-dart equation comes from the face-deletion schedule
produced by the ear statement, and the non-cancellation clause is the new
Prop.  These are the only inputs. -/
theorem estimatingPieceConstruction_of_earStatement
    (hear : Embedded.FaceSetEarStatement.{u, w, v})
    (hne : EstimatingPieceNonCancellationStatement.{u, w, v}) :
    EstimatingPieceConstructionStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta scaffold hred
  refine ⟨{ equations := ?_ }⟩
  intro edge
  have hpeeling : Embedded.FaceSetBoundaryPeeling
      edge.candidate.contiguity.boundary :=
    Embedded.faceSetBoundaryPeeling_of_earStatement hear
      edge.candidate.contiguity.boundary
  refine Embedded.CellPieceEquations.of_boundary_equation
    edge.candidate.contiguity edge.target_eq ?_ ?_
  · exact edge.candidate.contiguity.targetBoundary_value_of_pasting
      hpeeling.to_homotopy
  · exact hne D eps Delta scaffold hred edge edge.target edge.target_eq

/-! ## Model tests -/

/-- A diagram with at most one relator cell is reduced: the no-cancelling-pair
condition quantifies over a split exhibiting two distinct listed cells. -/
theorem reduced_of_rCellCount_le_one
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (h : Delta.rCellCount ≤ 1) :
    Delta.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  have h' : Delta.relatorCells.length ≤ 1 := h
  have hlen := congrArg List.length hsplit
  simp only [List.length_append, List.length_cons] at hlen
  exfalso
  omega

/-- Model test at the empty relator family: the Piece construction's target
structure is inhabited, because an interior edge carries a relator-cell index
and there is none. -/
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

/-- Model test of the new Prop at the empty relator family: its body holds for
the same reason. -/
theorem estimatingPieceNonCancellation_holds_of_rCellCount_zero
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hzero : Delta.rCellCount = 0)
    (hred : Delta.Reduced)
    (edge : Embedded.InteriorEdge scaffold.selected.family)
    (target : Fin Delta.rCellCount)
    (htarget : edge.candidate.contiguity.target = some target) :
    GGT.RelLetter.listVal
        (edge.candidate.contiguity.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.rightSide))⁻¹ *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.sourceArc.rotated) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.rightSide) := by
  exact absurd target.isLt (by omega)

/-- Model test at exactly one relator cell: every interior edge is
self-contiguous.  Together with `reduced_of_rCellCount_le_one` this locates the
remaining content of the new Prop: at one cell the reducedness hypothesis of
`EstimatingPieceConstructionStatement` is automatic, so the inequality there
cannot come from reducedness. -/
theorem interiorEdge_source_eq_target_of_rCellCount_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Embedded.Candidate D eps Delta)}
    (hone : Delta.rCellCount = 1)
    (edge : Embedded.InteriorEdge selected) :
    edge.candidate.contiguity.source = edge.target := by
  apply Fin.ext
  have h1 := edge.candidate.contiguity.source.isLt
  have h2 := edge.target.isLt
  omega

end VanKampen
end GGT
end GroupApproximation
