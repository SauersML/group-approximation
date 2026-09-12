import GroupApproximation.GGT.VanKampen.VanKampenMerge
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapse
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLeastAreaCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Ingredients of the O52 surgery at least area

Osin, arXiv:math/0411039v3, O52: in a least-area diagram, if a contiguity region
`Γ` of a relator cell `Π` to another relator cell `Σ` reads the same relator in the
same position, "we can cut the subdiagram … and fill the obtained hole with a
diagram without `R`-cells, reducing the number of `R`-cells by 2".  The surgery is
carried out by collapsing `Γ` into one G-face (`Surgery.InnerGRegion`) and merging
`Π`, that face and `Σ` by deleting one shared edge on each side
(`VanKampenData.exists_merge`).  This file collects the ingredients.

* `CombMap.IsFaceCycle.eq_of_head_eq`: a face cycle is determined by its head.
* `DiscDiagram.vanKampenData`, `DiscDiagram.relatorFaces_card`: a disc diagram gives
  van Kampen data with exactly `rCellCount` relator faces.
* `DiscDiagram.leastArea_listVal_word_ne_one`: a relator cell reading a trivial word
  contradicts least area.
* `Embedded.ContiguityGeometry.innerGRegion`: the collapsible G-region of a contiguity
  region at least area.
* `Embedded.CyclicArc.rotated_rotate_pred`, `Embedded.CyclicArc.eq_rotated_rotate_pred`:
  the face cycle of a cell starting at the last dart of an arc.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv HullSC RelatorDefectBudget

universe u w v

/-- **A face cycle is determined by its head.** -/
theorem CombMap.IsFaceCycle.eq_of_head_eq {M : CombMap.{v}} {l₁ l₂ : List M.Dart}
    (h₁ : M.IsFaceCycle l₁) (h₂ : M.IsFaceCycle l₂)
    (hhead : l₁.head h₁.ne_nil = l₂.head h₂.ne_nil) : l₁ = l₂ := by
  have e₁ := eq_orbitWalk_of_isChain M.facePerm l₁ (l₁.head h₁.ne_nil) h₁.chain
    (List.head?_eq_some_head h₁.ne_nil)
  have e₂ := eq_orbitWalk_of_isChain M.facePerm l₂ (l₂.head h₂.ne_nil) h₂.chain
    (List.head?_eq_some_head h₂.ne_nil)
  have hlen : l₁.length = l₂.length := by
    rw [h₁.length_eq, h₂.length_eq, hhead]
  rw [e₁, e₂, hlen, hhead]

namespace DiscDiagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

open scoped Classical in
/-- The faces carrying relator records. -/
noncomputable def relatorFaces (Delta : DiscDiagram.{u, w, v} W) :
    Finset Delta.toCombMap.Face :=
  (Delta.relatorCells.map RelatorCell.face).toFinset

theorem mem_relatorFaces {Delta : DiscDiagram.{u, w, v} W} {f : Delta.toCombMap.Face} :
    f ∈ Delta.relatorFaces ↔ ∃ C ∈ Delta.relatorCells, C.face = f := by
  rw [relatorFaces, List.mem_toFinset, List.mem_map]

/-- A disc diagram has exactly `rCellCount` relator faces. -/
theorem relatorFaces_card (Delta : DiscDiagram.{u, w, v} W) :
    Delta.relatorFaces.card = Delta.rCellCount := by
  show ((Delta.relatorCells.map RelatorCell.face).toFinset).card = Delta.relatorCells.length
  rw [List.toFinset_card_of_nodup Delta.relatorCell_faces_nodup, List.length_map]

/-- A relator face reads a relator. -/
theorem isSignedConjugate_faceWord_of_cell (Delta : DiscDiagram.{u, w, v} W)
    (C : RelatorCell Delta.toCombMap Delta.outerFace W) (hC : C ∈ Delta.relatorCells) :
    IsSignedConjugate (RelLetter.listVal '' W) (RelLetter.listVal (Delta.faceWord C.face)) := by
  rw [faceWord, ← Delta.relatorCell_word C hC]
  exact IsSignedConjugate.base ⟨C.word, C.word_mem, rfl⟩

/-- **The van Kampen data of a disc diagram**: its exterior face and its relator faces. -/
noncomputable def vanKampenData (Delta : DiscDiagram.{u, w, v} W) :
    VanKampenData (RelLetter.listVal '' W) Delta.toCombMap Delta.label where
  relFaces := Delta.relatorFaces
  outer := (Delta.faceBoundary Delta.outerFace).darts
  outer_cycle := (Delta.faceBoundary Delta.outerFace).isFaceCycle
  outer_not_mem := by
    rw [FaceBoundary.faceOf_head]
    intro h
    obtain ⟨C, _, hCf⟩ := mem_relatorFaces.mp h
    exact C.face_ne_outer hCf
  rel := by
    intro l hl hf
    obtain ⟨C, hC, hCf⟩ := mem_relatorFaces.mp hf
    obtain ⟨k, hk, hrot⟩ := (Delta.faceBoundary C.face).isFaceCycle.exists_rotate_eq hl
      ((FaceBoundary.faceOf_head _).trans hCf)
    rw [← hrot, List.map_rotate]
    exact isSignedConjugate_rotate _ (by rw [List.length_map]; exact hk)
      (Delta.isSignedConjugate_faceWord_of_cell C hC)
  triv := by
    intro l hl hO hnot
    have hO' : Delta.toCombMap.faceOf (l.head hl.ne_nil) ≠ Delta.outerFace := by
      rwa [FaceBoundary.faceOf_head] at hO
    rcases Delta.inner_face _ hO' with ⟨C, hC, hCf⟩ | hone
    · exact absurd (mem_relatorFaces.mpr ⟨C, hC, hCf⟩) hnot
    · obtain ⟨k, hk, hrot⟩ :=
        (Delta.faceBoundary (Delta.toCombMap.faceOf (l.head hl.ne_nil))).isFaceCycle.exists_rotate_eq
          hl (FaceBoundary.faceOf_head _)
      rw [← hrot, List.map_rotate]
      exact listVal_rotate_eq_one _ (by rw [List.length_map]; exact hk) hone

theorem vanKampenData_relFaces (Delta : DiscDiagram.{u, w, v} W) :
    Delta.vanKampenData.relFaces = Delta.relatorFaces := rfl

theorem vanKampenData_outer (Delta : DiscDiagram.{u, w, v} W) :
    Delta.vanKampenData.outer = (Delta.faceBoundary Delta.outerFace).darts := rfl

/-- **A relator cell reading a trivial word contradicts least area**: dropping its
factor fills the boundary with one relator fewer. -/
theorem leastArea_listVal_word_ne_one {Delta : DiscDiagram.{u, w, v} W}
    (hlea : Delta.LeastArea) (C : RelatorCell Delta.toCombMap Delta.outerFace W)
    (hC : C ∈ Delta.relatorCells) : RelLetter.listVal C.word ≠ 1 := by
  intro h1
  obtain ⟨s, t, hst⟩ := List.append_of_mem hC
  have hvalue : C.value = 1 := by
    unfold RelatorCell.value
    split <;> simp [h1]
  have hprod : ((s ++ t).map RelatorCell.value).prod = Delta.boundaryValue := by
    rw [← Delta.relatorValues_prod_eq_boundaryValue, hst]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, hvalue,
      one_mul]
  have hrp := RelatorDefectBudget.isRelatorProduct_prod_of_signedConjugates
    ((s ++ t).map RelatorCell.value) (fun x hx => by
      obtain ⟨C', _, rfl⟩ := List.mem_map.mp hx
      exact C'.value_isSignedConjugate)
  rw [hprod, List.length_map] at hrp
  have hle := hlea hrp
  have hcount : Delta.rCellCount = (s ++ t).length + 1 := by
    show Delta.relatorCells.length = _
    rw [hst]
    simp only [List.length_append, List.length_cons]
    omega
  omega

end DiscDiagram

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}

/-- **The collapsible G-region of a contiguity region at least area.**  No relator
record lies on its faces, since a relator cell reading a trivial word contradicts least
area. -/
noncomputable def ContiguityGeometry.innerGRegion (Gamma : ContiguityGeometry D eps Delta faces)
    (hlea : Delta.LeastArea) : Surgery.InnerGRegion Delta where
  faces := faces
  boundary := Gamma.boundary
  cells_avoid := fun C hC hCf => DiscDiagram.leastArea_listVal_word_ne_one hlea C hC (by
    have h := (Gamma.boundary.all_gCells C.face hCf).2
    rwa [DiscDiagram.faceWord, ← Delta.relatorCell_word C hC] at h)
  value_one := cycle_value_eq_one_of_shelling Gamma.boundary Gamma.pasting.choose_spec

theorem ContiguityGeometry.innerGRegion_faces (Gamma : ContiguityGeometry D eps Delta faces)
    (hlea : Delta.LeastArea) : (Gamma.innerGRegion hlea).faces = faces := rfl

/-- The rotation of an arc's carrier starting at the arc's last dart. -/
theorem CyclicArc.rotated_rotate_pred {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) (h : arc.darts ≠ []) :
    arc.rotated.rotate (arc.length - 1) =
      arc.darts.getLast h :: (arc.rotated.drop arc.length ++ arc.darts.dropLast) := by
  have hsplit : arc.rotated =
      arc.darts.dropLast ++ (arc.darts.getLast h :: arc.rotated.drop arc.length) := by
    calc arc.rotated = arc.darts ++ arc.rotated.drop arc.length :=
          (List.take_append_drop arc.length arc.rotated).symm
      _ = (arc.darts.dropLast ++ [arc.darts.getLast h]) ++ arc.rotated.drop arc.length := by
          rw [List.dropLast_append_getLast h]
      _ = _ := by simp only [List.append_assoc, List.singleton_append]
  have hlen : arc.darts.dropLast.length = arc.length - 1 := by
    rw [List.length_dropLast, arc.darts_length]
  rw [← hlen]
  conv_lhs => rw [hsplit]
  rw [List.rotate_append_length_eq]
  simp only [List.cons_append]

/-- **The face cycle of a cell starting at the last dart of an arc** reads the rest of
the cell after the arc, then the arc without its last dart. -/
theorem CyclicArc.eq_rotated_rotate_pred {M : CombMap.{v}} {f : M.Face}
    (B : FaceBoundary M f) (arc : CyclicArc B.darts) (h : arc.darts ≠ [])
    {l : List M.Dart} (hl : M.IsFaceCycle l) (hhead : l.head hl.ne_nil = arc.darts.getLast h) :
    l = arc.darts.getLast h :: (arc.rotated.drop arc.length ++ arc.darts.dropLast) := by
  have hcyc : M.IsFaceCycle (arc.rotated.rotate (arc.length - 1)) := by
    rw [arc.rotated_eq_rotate, List.rotate_rotate]
    exact B.isFaceCycle.rotate _
  have hh : (arc.rotated.rotate (arc.length - 1)).head hcyc.ne_nil = arc.darts.getLast h :=
    Option.some.inj ((List.head?_eq_some_head hcyc.ne_nil).symm.trans
      (by rw [arc.rotated_rotate_pred h]; rfl))
  rw [← arc.rotated_rotate_pred h]
  exact hl.eq_of_head_eq hcyc (hhead.trans hh.symm)

end Embedded

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsFaceCycle.eq_of_head_eq
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.vanKampenData
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.relatorFaces_card
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.leastArea_listVal_word_ne_one
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.innerGRegion
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.eq_rotated_rotate_pred
