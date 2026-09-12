import GroupApproximation.GGT.VanKampen.SurgeryCutDiagram
import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells
import GroupApproximation.Meta.AxiomGuard

/-!
# Collapsing an interior `G`-region of a disc diagram

`Surgery.MapCollapse.replaceGRegion` deletes every edge internal to a face set
and recloses the region as one face.  `SurgeryCutDiagram` retypes that map as a
`DiscDiagram` in the case where the collapsed set is the **complement** of a
piece, so the new face becomes the piece's outer face and relator cells are
lost.  This file does the other case, the one the drop branch of Osin's Lemma
6.5(a) needs: the collapsed region is **interior**, the outer face survives, no
relator cell is inside, and the diagram keeps every relator cell it had while
its face count drops.

The output is a `Surgery.OrderedGRegionReplacement`, the corrected replacement
interface of issue #205, **not** `Surgery.GRegionReplacement`.  That is not a
convenience: `SurgeryRCellEquivCounterexample.no_historical_transport` refutes
the full-type bijection `Surgery.RCellEquiv` asks for, at two explicit discs with
the same boundary and empty relator lists, and a face-dropping collapse is
exactly the situation where the two potential-record types differ.  A drop
branch stated with `GRegionReplacement` therefore asks for a datatype the
counterexample rules out; `Surgery.OrderedRCellTransport` asks only for the
ordered word and value lists, which a collapse preserves on the nose.

## What the producer supplies

`InteriorGCellRegion` has five fields and exactly one of them is geometry:

* `region` — the disc certificate `Surgery.MapCollapse.IsDiscRegion`;
* `outer_notMem` — the outer face is not collapsed;
* `cells` with `cells_eq` — every relator cell of `Delta` lies outside the
  region, presented as the ordered list itself so that the transport is a
  `List.map` rather than a `List.pmap`;
* `cycle_value` — **the merged face reads a word of value one.**

Only the last is Osin's geometry.  It is exactly the conclusion of
`Embedded.FaceSetBoundaryPeeling.cycle_value_eq_one`, so a producer that peels
the region's boundary cycle discharges it.  It is a hypothesis here, not an
assumption of the file: nothing below asserts it.

## What comes out

* `collapseDiagram` — the retyped `DiscDiagram`, with the outer face word, the
  ordered relator words and the ordered relator values all unchanged;
* `collapseReplacement` — the `OrderedGRegionReplacement`;
* `collapseReplacement_faceCount_lt` — the face count drops as soon as the
  region has at least two faces, which is what the face-count induction of
  `Estimating/Assembly.lean` consumes.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

open GroupApproximation.HullSC

universe u w v

/-! ## A list-level helper -/

/-- Mapping after forgetting a subtype proof is mapping the composite. -/
theorem map_subtypeVal_map {α β : Type*} {p : α → Prop}
    (l : List {a : α // p a}) (f : α → β) :
    l.map (fun d => f d.1) = (l.map Subtype.val).map f := by
  rw [List.map_map]; rfl

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}

/-! ## The producer's data -/

/-- **An interior `G`-region of a disc diagram.**  A disc region of faces that
avoids the outer face and every relator cell, whose boundary cycle reads a word
of value one. -/
structure InteriorGCellRegion (Delta : DiscDiagram.{u, w, v} W) where
  /-- The collapsed faces. -/
  faces : Finset Delta.toCombMap.Face
  /-- The topological disc certificate for the collapse. -/
  region : IsDiscRegion Delta.toCombMap faces
  /-- The outer face survives the collapse. -/
  outer_notMem : Delta.outerFace ∉ faces
  /-- The relator cells, each recorded as lying outside the region. -/
  cells : List {C : RelatorCell Delta.toCombMap Delta.outerFace W //
    C.face ∉ faces}
  /-- The recorded cells are exactly the diagram's ordered relator cells. -/
  cells_eq : cells.map Subtype.val = Delta.relatorCells
  /-- **The geometric input.**  The merged face reads a word of value one.
  `Embedded.FaceSetBoundaryPeeling.cycle_value_eq_one` produces it from a peel
  of the region's boundary cycle. -/
  cycle_value :
    GGT.RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle)
      = 1

namespace InteriorGCellRegion

variable {Delta : DiscDiagram.{u, w, v} W} (R : InteriorGCellRegion Delta)

/-! ## Face words are unchanged -/

/-- A surviving face reads the word it read before. -/
theorem faceWord_keptFace {g : Delta.toCombMap.Face} (hg : g ∉ R.faces) :
    ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
        (fun d => Delta.label d.1) = Delta.faceWord g := by
  have h := replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap R.faces
    R.region Delta.faceBoundary g hg
  calc ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
        (fun d => Delta.label d.1)
      = (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
          Subtype.val).map Delta.label := by
        rw [List.map_map]; rfl
    _ = Delta.faceWord g := by rw [h]; rfl

/-- The merged face reads the region's boundary cycle. -/
theorem faceWord_newFace :
    ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (newFace Delta.toCombMap R.faces R.region)).darts).map
        (fun d => Delta.label d.1) =
      Embedded.dartWord Delta R.region.toBoundaryCycle.cycle := by
  have h := replaceGRegionFaceBoundary_newFace_map_val Delta.toCombMap R.faces
    R.region Delta.faceBoundary
  calc ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (newFace Delta.toCombMap R.faces R.region)).darts).map
        (fun d => Delta.label d.1)
      = (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (newFace Delta.toCombMap R.faces R.region)).darts).map
          Subtype.val).map Delta.label := by
        rw [List.map_map]; rfl
    _ = Embedded.dartWord Delta R.region.toBoundaryCycle.cycle := by rw [h]; rfl

/-! ## The relator cells -/

/-- A relator cell of `Delta`, transported to the collapse.  The conjugator and
the orientation are untouched, so the based value is literally the same. -/
noncomputable def collapseCell
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ R.faces}) :
    RelatorCell (replaceGRegion Delta.toCombMap R.faces R.region)
      (keptFace Delta.toCombMap R.faces R.region Delta.outerFace
        R.outer_notMem) W where
  face := keptFace Delta.toCombMap R.faces R.region C.1.face C.2
  face_ne_outer := fun h =>
    C.1.face_ne_outer (keptFace_inj Delta.toCombMap R.faces R.region C.1.face
      Delta.outerFace C.2 R.outer_notMem h)
  word := C.1.word
  word_mem := C.1.word_mem
  conjugator := C.1.conjugator
  reversed := C.1.reversed

/-- The transported ordered relator-cell list. -/
noncomputable def collapseCells :
    List (RelatorCell (replaceGRegion Delta.toCombMap R.faces R.region)
      (keptFace Delta.toCombMap R.faces R.region Delta.outerFace
        R.outer_notMem) W) :=
  R.cells.map R.collapseCell

theorem collapseCells_map_word :
    (R.collapseCells).map RelatorCell.word =
      Delta.relatorCells.map RelatorCell.word := by
  have h1 : (R.collapseCells).map RelatorCell.word =
      R.cells.map (fun C => C.1.word) := by
    show ((R.cells.map R.collapseCell).map RelatorCell.word) = _
    rw [List.map_map]; rfl
  have h2 : (R.cells.map Subtype.val).map RelatorCell.word =
      R.cells.map (fun C => C.1.word) := by
    rw [List.map_map]; rfl
  rw [h1, ← R.cells_eq, h2]

theorem collapseCells_map_value :
    (R.collapseCells).map RelatorCell.value =
      Delta.relatorCells.map RelatorCell.value := by
  have h1 : (R.collapseCells).map RelatorCell.value =
      R.cells.map (fun C => C.1.value) := by
    show ((R.cells.map R.collapseCell).map RelatorCell.value) = _
    rw [List.map_map]; rfl
  have h2 : (R.cells.map Subtype.val).map RelatorCell.value =
      R.cells.map (fun C => C.1.value) := by
    rw [List.map_map]; rfl
  rw [h1, ← R.cells_eq, h2]

theorem cells_map_face_nodup :
    (R.cells.map (fun C => C.1.face)).Nodup := by
  have h := Delta.relatorCell_faces_nodup
  rw [← R.cells_eq, List.map_map] at h
  exact h

theorem cells_nodup : R.cells.Nodup :=
  List.Nodup.of_map _ R.cells_map_face_nodup

theorem collapseCells_faces_nodup :
    ((R.collapseCells).map RelatorCell.face).Nodup := by
  have h1 : (R.collapseCells).map RelatorCell.face =
      R.cells.map (fun C =>
        keptFace Delta.toCombMap R.faces R.region C.1.face C.2) := by
    show ((R.cells.map R.collapseCell).map RelatorCell.face) = _
    rw [List.map_map]; rfl
  rw [h1]
  refine List.Nodup.map_on ?_ R.cells_nodup
  intro x hx y hy hxy
  have hface : x.1.face = y.1.face :=
    keptFace_inj Delta.toCombMap R.faces R.region x.1.face y.1.face x.2 y.2 hxy
  exact List.inj_on_of_nodup_map R.cells_map_face_nodup hx hy hface

theorem mem_collapseCells
    {C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ R.faces}} (hC : C ∈ R.cells) :
    R.collapseCell C ∈ R.collapseCells :=
  List.mem_map.2 ⟨C, hC, rfl⟩

theorem val_mem_relatorCells
    {C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ R.faces}} (hC : C ∈ R.cells) :
    C.1 ∈ Delta.relatorCells := by
  rw [← R.cells_eq]
  exact List.mem_map.2 ⟨C, hC, rfl⟩

/-! ## The collapsed diagram -/

/-- **The collapse, as a disc diagram.** -/
noncomputable def collapseDiagram : DiscDiagram.{u, w, v} W where
  toCombMap := replaceGRegion Delta.toCombMap R.faces R.region
  planar := replaceGRegion_planar Delta.toCombMap R.faces R.region Delta.planar
  label := fun d => Delta.label d.1
  label_alpha := fun d => Delta.label_alpha d.1
  outerFace := keptFace Delta.toCombMap R.faces R.region Delta.outerFace
    R.outer_notMem
  faceBoundary := replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
    Delta.faceBoundary
  relatorCells := R.collapseCells
  relatorCell_faces_nodup := R.collapseCells_faces_nodup
  relatorCell_word := by
    intro C hC
    have hC' : C ∈ R.cells.map R.collapseCell := hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC'
    show C₀.1.word =
      ((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
        Delta.faceBoundary
        (keptFace Delta.toCombMap R.faces R.region C₀.1.face C₀.2)).darts).map
          (fun d => Delta.label d.1)
    rw [R.faceWord_keptFace C₀.2]
    exact Delta.relatorCell_word C₀.1 (R.val_mem_relatorCells hC₀)
  inner_face := by
    intro F hF
    by_cases hnew : F = newFace Delta.toCombMap R.faces R.region
    · right
      subst hnew
      show GGT.RelLetter.listVal
        (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (newFace Delta.toCombMap R.faces R.region)).darts).map
            (fun d => Delta.label d.1)) = 1
      rw [R.faceWord_newFace]
      exact R.cycle_value
    · obtain ⟨g, hg, rfl⟩ :=
        exists_keptFace_of_ne_newFace Delta.toCombMap R.faces R.region F hnew
      have hne : g ≠ Delta.outerFace := by
        intro hgo
        exact hF (keptFace_congr Delta.toCombMap R.faces R.region g
          Delta.outerFace hg R.outer_notMem hgo)
      rcases Delta.inner_face g hne with ⟨C₀, hC₀, hface⟩ | hone
      · left
        rw [← R.cells_eq] at hC₀
        obtain ⟨C₁, hC₁, hval⟩ := List.mem_map.1 hC₀
        refine ⟨R.collapseCell C₁, R.mem_collapseCells hC₁, ?_⟩
        show keptFace Delta.toCombMap R.faces R.region C₁.1.face C₁.2 =
          keptFace Delta.toCombMap R.faces R.region g hg
        refine keptFace_congr Delta.toCombMap R.faces R.region C₁.1.face g
          C₁.2 hg ?_
        rw [hval]
        exact hface
      · right
        show GGT.RelLetter.listVal
          (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
            Delta.faceBoundary
            (keptFace Delta.toCombMap R.faces R.region g hg)).darts).map
              (fun d => Delta.label d.1)) = 1
        rw [R.faceWord_keptFace hg]
        exact hone
  boundary_product := by
    show (R.collapseCells.map RelatorCell.value).prod =
      GGT.RelLetter.listVal (RelWord.revInv
        (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
          Delta.faceBoundary
          (keptFace Delta.toCombMap R.faces R.region Delta.outerFace
            R.outer_notMem)).darts).map (fun d => Delta.label d.1)))
    rw [R.collapseCells_map_value, R.faceWord_keptFace R.outer_notMem]
    exact Delta.boundary_product

/-! ## The replacement -/

theorem collapseDiagram_boundaryWord :
    (R.collapseDiagram).boundaryWord = Delta.boundaryWord := by
  show RelWord.revInv
      (((replaceGRegionFaceBoundary Delta.toCombMap R.faces R.region
        Delta.faceBoundary
        (keptFace Delta.toCombMap R.faces R.region Delta.outerFace
          R.outer_notMem)).darts).map (fun d => Delta.label d.1)) =
    RelWord.revInv (Delta.faceWord Delta.outerFace)
  rw [R.faceWord_keptFace R.outer_notMem]

theorem collapseTransport :
    Surgery.OrderedRCellTransport Delta (R.collapseDiagram) :=
  ⟨R.collapseCells_map_word, R.collapseCells_map_value⟩

/-- **The corrected `G`-region replacement produced by an interior collapse.** -/
noncomputable def collapseReplacement :
    Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta where
  diagram := R.collapseDiagram
  outerWord_eq := R.collapseDiagram_boundaryWord
  cells := R.collapseTransport

/-- **The face count drops** once the collapsed region has two faces. -/
theorem collapseReplacement_faceCount_lt (hcard : 2 ≤ R.faces.card) :
    (R.collapseReplacement).diagram.toCombMap.faceCount <
      Delta.toCombMap.faceCount :=
  replaceGRegion_faceCount_lt Delta.toCombMap R.faces R.region hcard

/-- The collapse keeps every relator cell, so a positive cell count survives. -/
theorem collapseDiagram_rCellCount :
    (R.collapseDiagram).rCellCount = Delta.rCellCount :=
  R.collapseTransport.rCellCount_eq

end InteriorGCellRegion

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.InteriorGCellRegion.collapseDiagram

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.InteriorGCellRegion.collapseReplacement

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.InteriorGCellRegion.collapseReplacement_faceCount_lt
