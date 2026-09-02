import GroupApproximation.GGT.KazhdanHypGirthEightDiagram
import GroupApproximation.GGT.VanKampen.CactusRealization

/-!
# Relator-cell coverage and identity reduction

This module isolates the presentation-independent part of base-cell
elimination.  Under explicit coverage of every inner face by a stored relator
cell, the original diagram is already relator-only, so its boundary word,
relator area, and reducedness are preserved by equality.

The face-count theorem also proves that free-group cells contribute zero to the
curvature count under the same hypothesis: `rCellCount = innerFaceCount`.
This is the base-cell step required before the triangular Euler estimate in
`KazhdanHypGirthEightFromDiagram`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

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

/-! ## Exact-boundary retyping of the cactus complement -/

/-- A cactus complement can be retyped away from the distinguished base cell
when an explicit relator-only retyping is supplied.  The fields record only
the boundary, area, and reducedness consequences used by a literal filling. -/
structure CactusRelatorRetyping
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v} W
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  relatorOnly : RelatorCellCover diagram
  rCellCount_le : diagram.rCellCount ≤ Delta.rCellCount
  reduced : diagram.Reduced

/-- The retyped cactus is an exact-boundary relator-only disc. -/
theorem exactBoundaryRelatorOnly_of_cactusRetyping
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (C : CactusRelatorRetyping Delta) :
    ∃ D : DiscDiagram.{u, w, v} W,
      D.boundaryWord = Delta.boundaryWord ∧
      RelatorCellCover D ∧ D.Reduced ∧ D.rCellCount ≤ Delta.rCellCount :=
  ⟨C.diagram, C.boundaryWord_eq, C.relatorOnly, C.reduced, C.rCellCount_le⟩

/-! ## Cancellation surgery output -/

/-- Output of cutting a mirror relator-cell pair and re-closing the
complementary boundary.  The area equation is the sole numerical fact needed
to turn the topological cut into a strict least-area contradiction. -/
structure MirrorPairCut
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  result : DiscDiagram.{u, w, v} W
  boundaryWord_eq : result.boundaryWord = Delta.boundaryWord
  relatorOnly : RelatorCellCover result
  reduced : result.Reduced
  area_eq : result.rCellCount + 2 = Delta.rCellCount

/-- A mirror-pair cut strictly lowers relator area. -/
theorem MirrorPairCut.area_lt
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (C : MirrorPairCut Delta) :
    C.result.rCellCount < Delta.rCellCount := by
  have harea := C.area_eq
  omega

/-- The exact-boundary output of a mirror-pair cut supplies the strict
area-decrease premise used by least-power reduction. -/
theorem exists_strict_cut_of_mirrorPairCut
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (C : MirrorPairCut Delta) :
    ∃ D : DiscDiagram.{u, w, v} W,
      D.boundaryWord = Delta.boundaryWord ∧ D.rCellCount < Delta.rCellCount :=
  ⟨C.result, C.boundaryWord_eq, C.area_lt⟩

/-! ## Degenerate model checks -/

/-- A zero-cell diagram cannot contain a mirror pair, so the cancellation
premise is empty in the one-face model. -/
theorem no_mirror_pair_of_empty_relatorCells
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (hzero : Delta.relatorCells = []) :
    ¬ ∃ C : RelatorCell Delta.toCombMap Delta.outerFace W,
      C ∈ Delta.relatorCells := by
  intro h
  obtain ⟨C, hC⟩ := h
  rw [hzero] at hC
  simp at hC

/-! ## Presentation-independent identity reduction -/

/-- A covered diagram needs no topological change: it is the required
relator-only output with literal boundary and area preserved by equality. -/
structure IdentityRelatorOnlyReduction
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  /-- The output diagram. -/
  diagram : DiscDiagram.{u, w, v} W
  /-- Its boundary word is literally unchanged. -/
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  /-- Its ordered relator area is literally unchanged. -/
  rCellCount_eq : diagram.rCellCount = Delta.rCellCount
  /-- Diagram reducedness is preserved. -/
  reduced : diagram.Reduced
  /-- Every output inner face is a stored relator cell. -/
  cover : RelatorCellCover diagram

/-- Explicit relator-cell coverage constructs the identity reduction. -/
def identityRelatorOnlyReduction
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (R : RelatorCellCover Delta)
    (hred : Delta.Reduced) : IdentityRelatorOnlyReduction Delta where
  diagram := Delta
  boundaryWord_eq := rfl
  rCellCount_eq := rfl
  reduced := hred
  cover := R

/-- The identity reduction preserves the sharp relator/inner-face count. -/
theorem identityRelatorOnlyReduction_count
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} (R : RelatorCellCover Delta)
    (hred : Delta.Reduced) :
    (identityRelatorOnlyReduction Delta R hred).diagram.rCellCount =
      (identityRelatorOnlyReduction Delta R hred).diagram.innerFaceCount :=
  R.rCellCount_eq_innerFaceCount

end VanKampen
end GGT
end GroupApproximation
