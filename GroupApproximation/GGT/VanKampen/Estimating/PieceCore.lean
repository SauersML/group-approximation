import GroupApproximation.GGT.VanKampen.Estimating.Incidence
import GroupApproximation.GGT.VanKampen.FaceSetPeelProducer

/-!
# The local core of the Piece construction

`Embedded.CellPieceEquations` has exactly three fields, and this module
accounts for all three at one embedded region.

* `target` and `target_eq` are supplied by the caller; on a selected interior
  edge they are stored in `Embedded.InteriorEdge` itself, so the
  outer-boundary case never reaches this construction.
* `arcs_value` is the boundary-dart count.  With the boundary cycle in its
  stored decomposition
  `sourceArc.reverse ++ rightSide ++ targetBoundary ++ leftSide`, the equation
  `target = right⁻¹ * source * left⁻¹` is exactly the statement that the cycle
  has trivial value, which a complete face-deletion schedule produces.
  `Contiguity.targetBoundary_value_of_pasting` performs that conversion and
  `FaceSetBoundaryPeeling.to_homotopy` supplies the schedule, so the only input
  is vk's `Embedded.FaceSetEarStatement`: every single-cycle `G`-region has an
  ear.  Nothing else in the peel is open.
* `whole_ne` is the non-cancellation inequality.  It is the whole content of
  `Embedded.ReducedCellPieceBridge`: that structure's other four fields are a
  free repackaging, since `sourceWord` and `targetWord` may be taken to be the
  arc words themselves and `connector` is pinned by `connector_value_eq`.  So
  the bridge is not a smaller input than the inequality, and this module names
  the inequality directly as `EstimatingPieceNonCancellationStatement`.

`Embedded.cellPieceEquations_of_earStatement` is the resulting per-region
constructor; `Estimating/PieceConstruction.lean` specializes it along a
scaffold to close `EstimatingPieceConstructionStatement`.

**Why the named Prop is not a consequence of `Delta.Reduced` alone.**
`Embedded.InteriorEdge` does not require the source cell to differ from the
target cell, and `DiscDiagram.Reduced` only constrains *pairs* of relator cells
occurring in the stored order.  `reduced_of_rCellCount_le_one` shows every
diagram with at most one relator cell is reduced, and
`interiorEdge_source_eq_target_of_rCellCount_one` shows that at exactly one
relator cell every interior edge is self-contiguous.  So at one cell the
reducedness hypothesis is automatic while the inequality is not, and any
producer of the named Prop must either exclude self-contiguous candidates or
derive the inequality from something other than `Delta.Reduced`.  This is
recorded as a model test, not as a refutation: it locates the remaining
content.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

/-- **The two-arc certificate at one embedded region.**  The boundary-dart
equation comes from the face-deletion schedule produced by the ear statement;
the non-cancellation clause is the only other input. -/
def cellPieceEquations_of_earStatement
    (hear : FaceSetEarStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {target : Fin Delta.rCellCount}
    (htarget : Gamma.target = some target)
    (hne : GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)) :
    CellPieceEquations Gamma :=
  CellPieceEquations.of_boundary_equation Gamma htarget
    (Gamma.targetBoundary_value_of_pasting
      (faceSetBoundaryPeeling_of_earStatement hear Gamma.boundary).to_homotopy)
    hne

end Embedded

/-! ## The single remaining local input -/

/-- **The one local inequality still missing from the Piece construction.**
For a reduced diagram, no selected interior candidate has its target relator
carrier equal to the source relator rotated and conjugated by the region's
short right side.  This is the `whole_ne` field of `CellPieceEquations` and
nothing more; the other two fields are proved above. -/
def EstimatingPieceNonCancellationStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (selected : Finset (Embedded.Candidate D eps Delta)),
    Delta.Reduced →
    ∀ (edge : Embedded.InteriorEdge selected)
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

/-- The landed reduced-bridge route supplies the named Prop.  The bridge stores
the same inequality once the target index is identified, which is the exact
sense in which the named Prop is no larger than the bridge family. -/
theorem estimatingPieceNonCancellation_of_reducedBridges
    (hbridge : ∀ {G : Type u} [Group G] {Lambda : Type w}
      (D : GGT.RelGenSet G Lambda) (eps : ℕ)
      {W : Set (List (GGT.RelLetter G Lambda))}
      (Delta : DiscDiagram.{u, w, v} W)
      (selected : Finset (Embedded.Candidate D eps Delta)),
      Delta.Reduced →
      ∀ edge : Embedded.InteriorEdge selected,
        Nonempty (Embedded.ReducedCellPieceBridge edge.candidate.contiguity)) :
    EstimatingPieceNonCancellationStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta selected hred edge target htarget
  obtain ⟨bridge⟩ := hbridge D eps Delta selected hred edge
  have hsome : some bridge.target = some target :=
    bridge.target_eq.symm.trans htarget
  have hidx : bridge.target = target := Option.some.inj hsome
  subst hidx
  exact bridge.whole_ne hred

/-! ## Model tests -/

/-- A diagram with at most one relator cell is reduced: the no-cancelling-pair
condition quantifies over a split exhibiting two listed cells. -/
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

/-- Model test at exactly one relator cell: every interior edge is
self-contiguous.  With `reduced_of_rCellCount_le_one` this locates the
remaining content of the named Prop, since reducedness is automatic there. -/
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

/-- Model test at the empty relator family: the body of the named Prop holds,
because an interior edge carries a relator-cell index and there is none. -/
theorem estimatingPieceNonCancellation_holds_of_rCellCount_zero
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (selected : Finset (Embedded.Candidate D eps Delta))
    (hzero : Delta.rCellCount = 0)
    (hred : Delta.Reduced)
    (edge : Embedded.InteriorEdge selected)
    (target : Fin Delta.rCellCount)
    (htarget : edge.candidate.contiguity.target = some target) :
    GGT.RelLetter.listVal
        (edge.candidate.contiguity.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.rightSide))⁻¹ *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.sourceArc.rotated) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          edge.candidate.contiguity.rightSide) :=
  absurd target.isLt (by omega)

end VanKampen
end GGT
end GroupApproximation
