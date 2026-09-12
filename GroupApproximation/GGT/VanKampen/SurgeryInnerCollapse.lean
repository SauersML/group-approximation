import GroupApproximation.GGT.VanKampen.SurgeryCutRecord
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity
import GroupApproximation.GGT.VanKampen.SurgeryCellMap
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.Meta.AxiomGuard

/-!
# Collapsing a G-cell region strictly inside a disc diagram

`Surgery.MapCollapse.RegionCutData.diagram` collapses the faces OUTSIDE a closed walk,
the exterior among them, and keeps the enclosed piece.  The surgeries of Osin's
Appendix (arXiv:math/0411039v3, §9: Lemma 9.4 Case 1, and the merges in the proof of
Lemma 9.7(a)) need the dual operation: collapse a union of G-cells lying strictly
inside the diagram into ONE G-face, keeping the exterior boundary and every relator
cell.  This file builds that diagram.

An `InnerGRegion` is a face set with an embedded boundary (`Embedded.FaceSetBoundary`,
which already makes every face a G-cell different from the exterior), no relator cell
among its faces, and a trivial boundary value.  The last field is what the collapse
cannot produce by itself: the new face must be a G-face, and `RegionShellingStatement`
(`FaceShelling.lean`) is open, so the producer supplies the value, typically through a
shelling (`InnerGRegion.ofShelling`).

The collapsed diagram (`InnerGRegion.diagram`) lives on
`MapCollapse.replaceGRegion` with the disc region of `FaceSetBoundary.toDiscRegion`.
Its exterior face is the kept old exterior, so the boundary word is unchanged
(`boundaryWord_eq`); its relator cells are the old cells on their kept faces, with the
old words, conjugators and orientations, in the old order (`cellMap`).  Hence the
collapse is an `OrderedGRegionReplacement` (`replacement`), O-equivalent
(`oEquivalent`), and preserves reducedness (`reduced`).  The new face reads the
region's boundary cycle (`newFace_word`) and is a G-face (`newFace_value`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery

open HullSC MapCollapse

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **A G-cell region strictly inside a disc diagram**, ready to be collapsed into one
G-face: an embedded boundary, no relator cell among its faces, trivial boundary value. -/
structure InnerGRegion (Delta : DiscDiagram.{u, w, v} W) where
  /-- The faces to collapse. -/
  faces : Finset Delta.toCombMap.Face
  /-- The embedded boundary of the region. -/
  boundary : Embedded.FaceSetBoundary Delta faces
  /-- No relator cell lies in the region. -/
  cells_avoid : ∀ C ∈ Delta.relatorCells, C.face ∉ faces
  /-- The boundary cycle reads a trivial element. -/
  value_one : RelLetter.listVal (Embedded.dartWord Delta boundary.cycle) = 1

namespace InnerGRegion

variable {Delta : DiscDiagram.{u, w, v} W}

/-- A shelled region has trivial boundary value. -/
def ofShelling (faces : Finset Delta.toCombMap.Face)
    (boundary : Embedded.FaceSetBoundary Delta faces)
    (cells_avoid : ∀ C ∈ Delta.relatorCells, C.face ∉ faces)
    {l : List Delta.toCombMap.Face}
    (shelling : Embedded.FaceShelling Delta faces l boundary.cycle) : InnerGRegion Delta where
  faces := faces
  boundary := boundary
  cells_avoid := cells_avoid
  value_one := Embedded.cycle_value_eq_one_of_shelling boundary shelling

variable (R : InnerGRegion Delta)

/-- The disc region the collapse uses, built from the embedded boundary walk. -/
def region : IsDiscRegion Delta.toCombMap R.faces := R.boundary.toDiscRegion

/-- The exterior face is not collapsed. -/
theorem outer_not_mem : Delta.outerFace ∉ R.faces :=
  fun h => (R.boundary.all_gCells _ h).1 rfl

open scoped Classical in
/-- Old faces to faces of the collapse: the collapsed faces go to the new face, every
other face to its kept copy. -/
noncomputable def faceMap (g : Delta.toCombMap.Face) :
    (replaceGRegion Delta.toCombMap R.faces R.region).Face :=
  if hg : g ∈ R.faces then newFace Delta.toCombMap R.faces R.region
  else keptFace Delta.toCombMap R.faces R.region g hg

theorem faceMap_of_mem {g : Delta.toCombMap.Face} (hg : g ∈ R.faces) :
    R.faceMap g = newFace Delta.toCombMap R.faces R.region := by
  simp [faceMap, hg]

theorem faceMap_of_not_mem {g : Delta.toCombMap.Face} (hg : g ∉ R.faces) :
    R.faceMap g = keptFace Delta.toCombMap R.faces R.region g hg := by
  simp [faceMap, hg]

/-- The image of a face other than the old exterior is not the kept exterior. -/
theorem faceMap_ne_outer {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace) :
    R.faceMap g ≠
      keptFace Delta.toCombMap R.faces R.region Delta.outerFace R.outer_not_mem := by
  by_cases h : g ∈ R.faces
  · rw [R.faceMap_of_mem h]
    exact (keptFace_ne_newFace Delta.toCombMap R.faces R.region _ R.outer_not_mem).symm
  · rw [R.faceMap_of_not_mem h]
    exact fun heq => hg (keptFace_inj Delta.toCombMap R.faces R.region _ _ h
      R.outer_not_mem heq)

/-- A relator record of the old diagram, on the image of its face, with its word,
conjugator and orientation unchanged. -/
noncomputable def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (replaceGRegion Delta.toCombMap R.faces R.region)
      (keptFace Delta.toCombMap R.faces R.region Delta.outerFace R.outer_not_mem) W where
  face := R.faceMap C.face
  face_ne_outer := R.faceMap_ne_outer C.face_ne_outer
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

/-- A kept face reads the old face word. -/
theorem keptFace_word (g : Delta.toCombMap.Face) (hg : g ∉ R.faces) :
    ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region Delta.faceBoundary
        (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
      (fun d => Delta.label d.1) = Delta.faceWord g := by
  have hmap := replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap
    R.faces R.region Delta.faceBoundary g hg
  calc ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region Delta.faceBoundary
          (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
        (fun d => Delta.label d.1)
      = (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region Delta.faceBoundary
            (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
          Subtype.val).map Delta.label := List.map_map.symm
    _ = ((Delta.faceBoundary g).darts).map Delta.label :=
        congrArg (fun l => l.map Delta.label) hmap
    _ = Delta.faceWord g := rfl

/-- The new face reads the boundary cycle of the region. -/
theorem newFace_word :
    ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region Delta.faceBoundary
        (newFace Delta.toCombMap R.faces R.region)).darts).map
      (fun d => Delta.label d.1) = Embedded.dartWord Delta R.boundary.cycle := by
  have hmap := replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap
    R.faces R.region Delta.faceBoundary
  calc ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region Delta.faceBoundary
          (newFace Delta.toCombMap R.faces R.region)).darts).map
        (fun d => Delta.label d.1)
      = (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region Delta.faceBoundary
            (newFace Delta.toCombMap R.faces R.region)).darts).map
          Subtype.val).map Delta.label := List.map_map.symm
    _ = (R.region.toBoundaryCycle.cycle).map Delta.label :=
        congrArg (fun l => l.map Delta.label) hmap
    _ = Embedded.dartWord Delta R.boundary.cycle := rfl

/-- The relator values are those of the old cells, in order. -/
theorem cells_value_map :
    (Delta.relatorCells.map R.cell).map RelatorCell.value =
      Delta.relatorCells.map RelatorCell.value := by
  rw [List.map_map]
  exact List.map_congr_left fun _ _ => rfl

/-- **The collapsed diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := replaceGRegion Delta.toCombMap R.faces R.region
  planar := replaceGRegion_planar Delta.toCombMap R.faces R.region Delta.planar
  label := fun d => Delta.label d.1
  label_alpha := fun d => Delta.label_alpha d.1
  outerFace := keptFace Delta.toCombMap R.faces R.region Delta.outerFace R.outer_not_mem
  faceBoundary := replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
    Delta.faceBoundary
  relatorCells := Delta.relatorCells.map R.cell
  relatorCell_faces_nodup := by
    have hmap : (Delta.relatorCells.map R.cell).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map R.faceMap := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [hmap]
    refine List.Nodup.map_on ?_ Delta.relatorCell_faces_nodup
    intro x hx y hy hxy
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hy
    rw [R.faceMap_of_not_mem (R.cells_avoid C hC),
      R.faceMap_of_not_mem (R.cells_avoid C' hC')] at hxy
    exact keptFace_inj Delta.toCombMap R.faces R.region _ _ _ _ hxy
  relatorCell_word := by
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    change C.word = ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
      Delta.faceBoundary (R.faceMap C.face)).darts).map (fun d => Delta.label d.1)
    rw [R.faceMap_of_not_mem (R.cells_avoid C hC), R.keptFace_word C.face (R.cells_avoid C hC)]
    exact Delta.relatorCell_word C hC
  inner_face := by
    intro F hF
    by_cases hnew : F = newFace Delta.toCombMap R.faces R.region
    · right
      subst hnew
      rw [R.newFace_word]
      exact R.value_one
    · obtain ⟨g, hg, rfl⟩ :=
        exists_keptFace_of_ne_newFace Delta.toCombMap R.faces R.region F hnew
      have hgo : g ≠ Delta.outerFace := fun h =>
        hF (keptFace_congr Delta.toCombMap R.faces R.region _ _ hg R.outer_not_mem h)
      rcases Delta.inner_face g hgo with ⟨C, hC, hface⟩ | hone
      · left
        refine ⟨R.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change R.faceMap C.face = keptFace Delta.toCombMap R.faces R.region g hg
        rw [R.faceMap_of_not_mem (R.cells_avoid C hC)]
        exact keptFace_congr Delta.toCombMap R.faces R.region _ _ _ _ hface
      · right
        rw [R.keptFace_word g hg]
        exact hone
  boundary_product :=
    (congrArg List.prod R.cells_value_map).trans
      (Delta.boundary_product.trans
        (congrArg (fun l => RelLetter.listVal (RelWord.revInv l))
          (R.keptFace_word Delta.outerFace R.outer_not_mem).symm))

/-- The exterior boundary word is unchanged. -/
theorem boundaryWord_eq : R.diagram.boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv (R.keptFace_word Delta.outerFace R.outer_not_mem)

/-- The ordered relator cells are the old ones, on the images of their faces. -/
noncomputable def cellMap : OrderedRCellMap Delta R.diagram R.faceMap where
  cell := R.cell
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- **The collapse is a G-region replacement.** -/
noncomputable def replacement : OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨R.diagram, R.boundaryWord_eq, R.cellMap.orderedTransport⟩

/-- The collapse is O-equivalent to the old diagram. -/
noncomputable def oEquivalent : OEquivalentDiscDiagram Delta R.diagram :=
  R.replacement.oEquivalent

/-- The collapse keeps the number of relator cells. -/
theorem rCellCount_eq : R.diagram.rCellCount = Delta.rCellCount :=
  R.cellMap.orderedTransport.rCellCount_eq

/-- Reducedness survives the collapse. -/
theorem reduced (hred : Delta.Reduced) : R.diagram.Reduced :=
  R.cellMap.orderedTransport.reduced hred

/-- The new face is not the exterior of the collapse. -/
theorem newFace_ne_outer :
    newFace Delta.toCombMap R.faces R.region ≠ R.diagram.outerFace :=
  (keptFace_ne_newFace Delta.toCombMap R.faces R.region _ R.outer_not_mem).symm

/-- The new face is a G-face of the collapse. -/
theorem newFace_value :
    RelLetter.listVal (R.diagram.faceWord (newFace Delta.toCombMap R.faces R.region)) = 1 := by
  change RelLetter.listVal (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
    Delta.faceBoundary (newFace Delta.toCombMap R.faces R.region)).darts).map
      (fun d => Delta.label d.1)) = 1
  rw [R.newFace_word]
  exact R.value_one

end InnerGRegion
end GroupApproximation.GGT.VanKampen.Surgery

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.cellMap
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.replacement
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.newFace_value
