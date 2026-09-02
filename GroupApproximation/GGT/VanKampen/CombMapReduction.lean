import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives

/-!
# Relator-cell coverage and identity reduction

For an ordinary triangular presentation, the local curvature input
`TriangularDiagramLocalData` already excludes free-group base cells: its
`innerFaceCell` field says that every non-outer face is one of the stored
relator cells.  This module proves the cheapest sufficient form of base-cell
elimination.  Under that coverage hypothesis the original diagram itself is a
`RelatorOnlyReduction`, so its boundary word, relator area, and reducedness are
preserved by equality.

The face-count theorem also proves that free-group cells contribute zero to the
curvature count under the same hypothesis: `rCellCount = innerFaceCount`.
This is the base-cell step required before the triangular Euler estimate in
`KazhdanHypGirthEightFromDiagram`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface

universe u w v

/-! ## Generic coverage by stored relator cells -/

/-- Every non-outer face of a disc diagram is represented by a stored relator
cell.  For triangular presentations this is the first field of
`TriangularDiagramLocalData`. -/
structure RelatorCellCover
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : Prop where
  /-- A non-outer face has a stored relator cell with exactly that face. -/
  cell : ∀ f, f ≠ Delta.outerFace →
    ∃ C ∈ Delta.relatorCells, C.face = f

namespace RelatorCellCover

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- Coverage by stored cells identifies membership in the relator-face list
with membership among all inner faces. -/
theorem relatorFace_mem_iff_innerFace (R : RelatorCellCover Delta)
    (f : Delta.toCombMap.Face) :
    f ∈ Delta.relatorCells.map RelatorCell.face ↔ f ∈ Delta.innerFaces := by
  constructor
  · intro hf
    obtain ⟨C, hCmem, hCface⟩ := List.mem_map.mp hf
    subst f
    simpa only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton] using C.face_ne_outer
  · intro hf
    have hfne : f ≠ Delta.outerFace := by
      simpa only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ,
        true_and, Finset.mem_singleton] using hf
    obtain ⟨C, hCmem, hCface⟩ := R.cell f hfne
    apply List.mem_map.mpr
    exact ⟨C, hCmem, hCface⟩

/-- If every inner face is a stored relator cell, relator area equals the full
inner-face count.  Thus no free-group face enters the curvature estimate. -/
theorem rCellCount_eq_innerFaceCount (R : RelatorCellCover Delta) :
    Delta.rCellCount = Delta.innerFaceCount := by
  classical
  have hfaces : (Delta.relatorCells.map RelatorCell.face).toFinset =
      Delta.innerFaces := by
    ext f
    rw [List.mem_toFinset]
    exact R.relatorFace_mem_iff_innerFace f
  calc
    Delta.rCellCount =
        (Delta.relatorCells.map RelatorCell.face).length := by
      simp only [DiscDiagram.rCellCount, List.length_map]
    _ = (Delta.relatorCells.map RelatorCell.face).toFinset.card :=
      (List.toFinset_card_of_nodup Delta.relatorCell_faces_nodup).symm
    _ = Delta.innerFaces.card := congrArg Finset.card hfaces
    _ = Delta.innerFaceCount := rfl

/-- The count equality sharpens the generic inequality
`rCellCount ≤ innerFaceCount`. -/
theorem innerFaceCount_le_rCellCount (R : RelatorCellCover Delta) :
    Delta.innerFaceCount ≤ Delta.rCellCount := by
  rw [R.rCellCount_eq_innerFaceCount]

end RelatorCellCover

/-! ## Triangular presentations -/

section Triangle

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {Delta : DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The relator-only interface implies generic stored-cell coverage. -/
theorem RelatorCellCover.ofRelatorOnly (R : RelatorOnly T Delta) :
    RelatorCellCover Delta where
  cell := R.cell

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- Local triangular diagram data implies generic stored-cell coverage. -/
theorem RelatorCellCover.ofLocalData (L : TriangularDiagramLocalData T Delta) :
    RelatorCellCover Delta where
  cell := L.innerFaceCell

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- Local triangular diagram data already excludes all free-group base cells. -/
theorem relatorOnlyOfLocalData (L : TriangularDiagramLocalData T Delta) :
    RelatorOnly T Delta where
  cell := L.innerFaceCell

/-- Under local triangular data, the identity diagram is the required
relator-only reduction.  Boundary and area preservation are reflexive. -/
def identityRelatorOnlyReduction (L : TriangularDiagramLocalData T Delta)
    (hred : Delta.Reduced) : RelatorOnlyReduction T Delta where
  diagram := Delta
  boundaryWord_eq := rfl
  rCellCount_le := le_rfl
  reduced := hred
  relatorOnly := relatorOnlyOfLocalData L

/-- Under an explicit relator-only hypothesis, the identity diagram is the
required reduction. -/
def identityRelatorOnlyReductionOfRelatorOnly (R : RelatorOnly T Delta)
    (hred : Delta.Reduced) : RelatorOnlyReduction T Delta where
  diagram := Delta
  boundaryWord_eq := rfl
  rCellCount_le := le_rfl
  reduced := hred
  relatorOnly := R

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The triangular local-data hypothesis makes relator area equal the number
of inner faces used by the Euler estimate. -/
theorem rCellCount_eq_innerFaceCount_ofLocalData
    (L : TriangularDiagramLocalData T Delta) :
    Delta.rCellCount = Delta.innerFaceCount :=
  (RelatorCellCover.ofLocalData L).rCellCount_eq_innerFaceCount

/-- Consequently the sharp curvature estimate can be stated directly for
relator-cell area without deleting any face. -/
theorem rCellCount_add_eight_le_three_mul_boundaryLength
    {d : ℕ} (hchecks : GirthEightChecks T d)
    (L : TriangularDiagramLocalData T Delta) :
    Delta.rCellCount + 8 ≤ 3 * Delta.combinatorialBoundaryLength := by
  rw [rCellCount_eq_innerFaceCount_ofLocalData L]
  exact L.innerFaceCount_add_eight_le_three_mul_boundaryLength hchecks

end Triangle

/-! ## Model tests -/

/-- The outer-only one-edge disc from the primitive module has relator-cell
coverage vacuously. -/
theorem oneEdgeRelatorCellCover : RelatorCellCover GirthEightPrimitives.oneEdgeDiagram where
  cell f hf := (hf (GirthEightPrimitives.oneEdge_face_eq f)).elim

/-- The model has both relator area and inner-face count equal to zero. -/
theorem oneEdge_rCellCount_eq_innerFaceCount :
    GirthEightPrimitives.oneEdgeDiagram.rCellCount =
      GirthEightPrimitives.oneEdgeDiagram.innerFaceCount :=
  oneEdgeRelatorCellCover.rCellCount_eq_innerFaceCount

/-- The identity reduction has exactly the original model boundary word. -/
theorem oneEdge_identity_boundaryWord :
    (identityRelatorOnlyReductionOfRelatorOnly
      (T := GirthEightPrimitives.emptyTriangleTable)
      { cell := oneEdgeRelatorCellCover.cell }
      GirthEightPrimitives.oneEdgeDiagram_reduced).diagram.boundaryWord =
      GirthEightPrimitives.oneEdgeDiagram.boundaryWord :=
  rfl

end VanKampen
end GGT
end GroupApproximation
