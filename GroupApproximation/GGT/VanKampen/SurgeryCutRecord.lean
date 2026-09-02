import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.GGT.VanKampen.SurgeryCutCells

/-!
# The data of a region cut

Osin's Lemma 6.5 cuts out the subdiagram enclosed by a four-arc closed walk.
That cut is a collapse of the COMPLEMENT: the faces outside the piece, the outer
face among them, are collapsed by `replaceGRegion`, and the collapsed outside
becomes the piece's outer face with the enclosing walk as its word.

`RegionCutData` is what a producer supplies for one such cut.  The disc region
on the complementary face set is the planar content, and the shelling of the
enclosed faces along the walk is the certificate that makes the piece's boundary
product a theorem rather than an assumption.  The kept relator cells are an
infix of the source's ordered cells, rebased at the basepoint of the walk, which
is what makes reducedness pass to the piece.

This file records the data and the bridges every field of the piece is built
from.  The boundary product is proved separately, and the piece itself is
assembled after that.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

open GroupApproximation.HullSC

universe u w v

/-- A face of a replacement that is not the new face is a kept face. -/
theorem exists_keptFace_of_ne_newFace (M : CombMap.{v}) (faces : Finset M.Face)
    (region : IsDiscRegion M faces)
    (F : (replaceGRegion M faces region).Face)
    (hF : F ≠ newFace M faces region) :
    ∃ (g : M.Face) (hg : g ∉ faces), F = keptFace M faces region g hg := by
  have hsymm := (replaceGRegionFaceEquiv M faces region).symm_apply_apply F
  rcases hs : replaceGRegionFaceEquiv M faces region F with ⟨g, hg⟩ | u
  · refine ⟨g, hg, ?_⟩
    rw [hs] at hsymm
    exact hsymm.symm
  · exfalso
    apply hF
    rw [hs] at hsymm
    exact hsymm.symm

/-- The data a producer supplies to cut out the subdiagram enclosed by a closed
walk. -/
structure RegionCutData {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  /-- The faces cut away, the outer face among them. -/
  outside : Finset Delta.toCombMap.Face
  /-- The old exterior is cut away, so the piece gets a new exterior. -/
  outer_mem : Delta.outerFace ∈ outside
  /-- The planar content: the cut-away faces are a disc region whose boundary
  cycle is the enclosing walk, read with the cut-away side on the dart. -/
  region : IsDiscRegion Delta.toCombMap outside
  /-- The faces enclosed by the walk. -/
  enclosed : Finset Delta.toCombMap.Face
  /-- The value of the path from the source basepoint to the basepoint on the
  walk. -/
  basepoint : G
  /-- The relator cells the cut keeps. -/
  cells : List {C : RelatorCell Delta.toCombMap Delta.outerFace W //
    C.face ∉ outside}
  /-- The ordered cells before the kept block. -/
  before : List (RelatorCell Delta.toCombMap Delta.outerFace W)
  /-- The ordered cells after the kept block. -/
  after : List (RelatorCell Delta.toCombMap Delta.outerFace W)
  /-- The kept cells are an infix of the source's ordered cells. -/
  cells_infix : Delta.relatorCells =
    before ++ cells.map Subtype.val ++ after
  /-- Every cell outside the kept block has a cut-away face. -/
  cut_faces : ∀ C ∈ before ++ after, C.face ∈ outside
  /-- Osin's clause (ii): the cut drops at least one relator cell. -/
  dropped : before ++ after ≠ []
  /-- The enclosing walk, cut into arcs in order. -/
  arcs : List (List Delta.toCombMap.Dart)
  /-- The arcs read the walk. -/
  arcs_flatten : region.toBoundaryCycle.cycle = arcs.flatten
  /-- The certificate that the walk bounds the enclosed faces: a shelling of
  them along the walk whose recorded steps are the kept cells, rebased. -/
  shelling : Embedded.CellShelling Delta enclosed
    (cells.map (fun C => basepoint⁻¹ * C.1.conjugator))
    (cells.map (fun C =>
      Embedded.orientedFaceDarts Delta C.1.face C.1.reversed))
    (Embedded.invDarts Delta region.toBoundaryCycle.cycle)

namespace RegionCutData

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- Every kept cell is a cell of the source. -/
theorem cells_mem (cut : RegionCutData Delta)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ cut.outside}) (hC : C ∈ cut.cells) :
    C.1 ∈ Delta.relatorCells := by
  rw [cut.cells_infix]
  refine List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ?_)))
  exact List.mem_map.2 ⟨C, hC, rfl⟩

/-- The kept cells have distinct faces. -/
theorem cells_faces_nodup (cut : RegionCutData Delta) :
    (cut.cells.map (fun C => C.1.face)).Nodup := by
  have h := Delta.relatorCell_faces_nodup
  rw [cut.cells_infix, List.map_append, List.map_append] at h
  have h2 := h.of_append_left.of_append_right
  rw [List.map_map] at h2
  exact h2

/-- The kept cells are pairwise distinct. -/
theorem cells_nodup (cut : RegionCutData Delta) : cut.cells.Nodup :=
  cut.cells_faces_nodup.of_map _

/-- The rebased cells of the piece have distinct faces. -/
theorem keptCells_faces_nodup (cut : RegionCutData Delta) :
    ((cut.cells.map
      (keptRelatorCell Delta cut.outside cut.region cut.basepoint)).map
        RelatorCell.face).Nodup := by
  rw [List.map_map]
  refine List.Nodup.map_on ?_ cut.cells_nodup
  intro x hx y hy hxy
  have hface : x.1.face = y.1.face :=
    keptFace_inj Delta.toCombMap cut.outside cut.region x.1.face y.1.face
      x.2 y.2 hxy
  exact List.inj_on_of_nodup_map cut.cells_faces_nodup x hx y hy hface

/-- The cut keeps fewer relator cells than the source has. -/
theorem rCellCount_lt (cut : RegionCutData Delta) :
    cut.cells.length < Delta.rCellCount := by
  have hlen := congrArg List.length cut.cells_infix
  simp only [List.length_append, List.length_map] at hlen
  have hpos : 0 < (cut.before ++ cut.after).length :=
    List.length_pos_iff.2 cut.dropped
  simp only [List.length_append] at hpos
  rw [DiscDiagram.rCellCount]
  omega

/-! ## The words of the piece's faces -/

/-- A kept face of the piece reads the old face's word. -/
theorem keptFaceWord (cut : RegionCutData Delta) (g : Delta.toCombMap.Face)
    (hg : g ∉ cut.outside) :
    ((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
        Delta.faceBoundary
        (keptFace Delta.toCombMap cut.outside cut.region g hg)).darts).map
      (fun d => Delta.label d.1) = Delta.faceWord g := by
  have hmap := replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap
    cut.outside cut.region Delta.faceBoundary g hg
  rw [DiscDiagram.faceWord, ← hmap, List.map_map]

/-- The new face of the piece reads the enclosing walk. -/
theorem newFaceWord (cut : RegionCutData Delta) :
    ((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
        Delta.faceBoundary
        (newFace Delta.toCombMap cut.outside cut.region)).darts).map
      (fun d => Delta.label d.1) =
      Embedded.dartWord Delta cut.region.toBoundaryCycle.cycle := by
  have hmap := replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap
    cut.outside cut.region Delta.faceBoundary
  rw [Embedded.dartWord, ← hmap, List.map_map]

/-- A kept cell's word is the word of its face in the piece. -/
theorem keptCells_word (cut : RegionCutData Delta)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ cut.outside}) (hC : C ∈ cut.cells) :
    (keptRelatorCell Delta cut.outside cut.region cut.basepoint C).word =
      ((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
          Delta.faceBoundary
          (keptRelatorCell Delta cut.outside cut.region cut.basepoint C).face
        ).darts).map (fun d => Delta.label d.1) := by
  have hword : C.1.word = Delta.faceWord C.1.face :=
    Delta.relatorCell_word C.1 (cut.cells_mem C hC)
  have hface := cut.keptFaceWord C.1.face C.2
  rw [hface]
  exact hword

/-- The source word of a kept cell is the word of its old face. -/
theorem cells_word (cut : RegionCutData Delta)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ cut.outside}) (hC : C ∈ cut.cells) :
    C.1.word = Delta.faceWord C.1.face :=
  Delta.relatorCell_word C.1 (cut.cells_mem C hC)

end RegionCutData
end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
