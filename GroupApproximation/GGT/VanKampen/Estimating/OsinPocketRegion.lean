import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPart
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket region of a disc diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, to which the induction applies when it keeps a relator cell.

A pocket region of `Δ` is a face set away from the exterior face such that the face set and
its complement are both disc regions, and the boundary cycle of the complement, reversed, is a
rotation of the boundary cycle of the face set.  Collapsing the complement into one exterior
face gives the pocket as a van Kampen diagram, whose relator faces are the relator cells of
`Δ` inside the face set.  No shelling is used.

* `isRelatorProduct_listVal_of_rotate`: rotating a word conjugates its value, so a relator
  budget of a rotation is one of the word.
* `PocketRegion.diagram`: the pocket as a disc diagram.
* `PocketRegion.diagram_boundaryWord`: it reads the word along the inverse of the boundary
  cycle of the complement.
* `PocketRegion.diagram_rCellCount_le`: it has at most as many relator cells as `Δ` has inside
  the face set.
* `PocketRegion.diagram_leastArea`: the pocket of a least-area diagram is least area, by
  `DiscDiagram.LeastArea.length_filter_mem_le` (`OsinPocketOuterPart`).
* `PocketRegion.diagram_rCellCount_pos` and `PocketRegion.diagram_rCellCount_lt`: a relator
  cell inside the face set gives a relator cell of the pocket, and one outside gives fewer
  cells than `Δ`.
* `PocketRegion.diagram_leastAreaCut`: the three together.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A relator budget of a rotation is one of the word.**  Rotating a word conjugates its
value by the value of the moved prefix. -/
theorem isRelatorProduct_listVal_of_rotate {R : Set G} {m : ℕ}
    (l : List (RelLetter G Lambda)) (k : ℕ)
    (h : RelatorDefectBudget.IsRelatorProduct R m (RelLetter.listVal (l.rotate k))) :
    RelatorDefectBudget.IsRelatorProduct R m (RelLetter.listVal l) := by
  have happ : ∀ a b : List (RelLetter G Lambda),
      RelLetter.listVal (a ++ b) = RelLetter.listVal a * RelLetter.listVal b := fun a b => by
    show ((a ++ b).map RelLetter.val).prod =
      (a.map RelLetter.val).prod * (b.map RelLetter.val).prod
    rw [List.map_append, List.prod_append]
  rw [List.rotate_eq_drop_append_take_mod, happ] at h
  have hconj := h.conj (RelLetter.listVal (l.take (k % l.length)))
  have hl : RelLetter.listVal l =
      RelLetter.listVal (l.take (k % l.length)) * RelLetter.listVal (l.drop (k % l.length)) := by
    rw [← happ, List.take_append_drop]
  have heq : RelLetter.listVal (l.take (k % l.length)) *
        (RelLetter.listVal (l.drop (k % l.length)) * RelLetter.listVal (l.take (k % l.length))) *
        (RelLetter.listVal (l.take (k % l.length)))⁻¹ = RelLetter.listVal l := by
    rw [hl]
    group
  rw [heq] at hconj
  exact hconj

/-- **A pocket region** of a disc diagram: a face set away from the exterior face whose face
set and complement are disc regions, with the boundary cycle of the complement, reversed, a
rotation of the boundary cycle of the face set. -/
structure PocketRegion {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) where
  /-- The faces of the pocket. -/
  faces : Finset Delta.toCombMap.Face
  /-- The faces outside the pocket. -/
  outside : Finset Delta.toCombMap.Face
  mem_outside_iff : ∀ f, f ∈ outside ↔ f ∉ faces
  outerFace_mem : Delta.outerFace ∈ outside
  /-- The pocket is a disc region. -/
  inner : IsDiscRegion Delta.toCombMap faces
  /-- The complement of the pocket is a disc region. -/
  outer : IsDiscRegion Delta.toCombMap outside
  /-- The boundary cycles of the pocket and of its complement are reverse to each other. -/
  invDarts_outer_rotate : ∃ k : ℕ, Embedded.invDarts Delta outer.cycle = inner.cycle.rotate k

namespace PocketRegion

variable {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

theorem outerFace_not_mem (P : PocketRegion Delta) : Delta.outerFace ∉ P.faces :=
  (P.mem_outside_iff _).mp P.outerFace_mem

theorem not_mem_outside (P : PocketRegion Delta) {f : Delta.toCombMap.Face}
    (hf : f ∈ P.faces) : f ∉ P.outside :=
  fun h => (P.mem_outside_iff f).mp h hf

theorem mem_faces_of_not_mem_outside (P : PocketRegion Delta) {f : Delta.toCombMap.Face}
    (hf : f ∉ P.outside) : f ∈ P.faces := by
  by_contra h
  exact hf ((P.mem_outside_iff f).mpr h)

open scoped Classical in
/-- The faces of the collapsed complement carrying the relator cells of `Δ` inside the
pocket. -/
noncomputable def cellFaces (P : PocketRegion Delta) :
    Finset (replaceGRegion Delta.toCombMap P.outside P.outer).Face :=
  ((Delta.relatorCells.filter (fun C => C.face ∈ P.faces)).map
    (fun C => if hC : C.face ∈ P.outside then newFace Delta.toCombMap P.outside P.outer
      else keptFace Delta.toCombMap P.outside P.outer C.face hC)).toFinset

open scoped Classical in
theorem newFace_not_mem_cellFaces (P : PocketRegion Delta) :
    newFace Delta.toCombMap P.outside P.outer ∉ P.cellFaces := by
  unfold cellFaces
  rw [List.mem_toFinset]
  intro hmem
  obtain ⟨C, hC, hCF⟩ := List.mem_map.mp hmem
  have hCout : C.face ∉ P.outside :=
    P.not_mem_outside (by simpa using (List.mem_filter.mp hC).2)
  simp only [dif_neg hCout] at hCF
  exact keptFace_ne_newFace Delta.toCombMap P.outside P.outer C.face hCout hCF

open scoped Classical in
theorem cellFaces_word_mem (P : PocketRegion Delta) :
    ∀ f ∈ P.cellFaces,
      ((replaceGRegionFaceBoundary Delta.toCombMap P.outside P.outer Delta.faceBoundary
        f).darts).map (fun d => Delta.label d.1) ∈ W := by
  intro f hf
  unfold cellFaces at hf
  rw [List.mem_toFinset] at hf
  obtain ⟨C, hC, hCF⟩ := List.mem_map.mp hf
  have hC' := List.mem_filter.mp hC
  have hCout : C.face ∉ P.outside := P.not_mem_outside (by simpa using hC'.2)
  simp only [dif_neg hCout] at hCF
  subst hCF
  rw [replaceGRegionFaceBoundary_keptFace_word Delta P.outside P.outer C.face hCout,
    DiscDiagram.faceWord, ← Delta.relatorCell_word C hC'.1]
  exact C.word_mem

open scoped Classical in
theorem cellFaces_triv (P : PocketRegion Delta) :
    ∀ f, f ≠ newFace Delta.toCombMap P.outside P.outer → f ∉ P.cellFaces →
      RelLetter.listVal (((replaceGRegionFaceBoundary Delta.toCombMap P.outside P.outer
        Delta.faceBoundary f).darts).map (fun d => Delta.label d.1)) = 1 := by
  intro f hf hnot
  obtain ⟨g, hg, rfl⟩ := exists_keptFace_of_ne_newFace Delta.toCombMap P.outside P.outer f hf
  rw [replaceGRegionFaceBoundary_keptFace_word Delta P.outside P.outer g hg]
  have hgin : g ∈ P.faces := P.mem_faces_of_not_mem_outside hg
  have hgo : g ≠ Delta.outerFace := fun h => hg (by rw [h]; exact P.outerFace_mem)
  rcases Delta.inner_face g hgo with ⟨C, hC, hCg⟩ | hone
  · exfalso
    apply hnot
    unfold cellFaces
    rw [List.mem_toFinset]
    subst hCg
    exact List.mem_map.mpr ⟨C, List.mem_filter.mpr ⟨hC, by simpa using hgin⟩, dif_neg hg⟩
  · exact hone

/-- **The pocket as a van Kampen diagram.**  Collapse the complement of the pocket into one
exterior face; the relator faces are the kept faces of the relator cells inside. -/
noncomputable def diagram (P : PocketRegion Delta) : DiscDiagram.{u, w, v} W :=
  DiscDiagram.ofPlanar (replaceGRegion Delta.toCombMap P.outside P.outer)
    (replaceGRegion_planar Delta.toCombMap P.outside P.outer Delta.planar)
    (fun d => Delta.label d.1) (fun d => Delta.label_alpha d.1)
    (newFace Delta.toCombMap P.outside P.outer)
    (replaceGRegionFaceBoundary Delta.toCombMap P.outside P.outer Delta.faceBoundary)
    P.cellFaces P.newFace_not_mem_cellFaces P.cellFaces_word_mem P.cellFaces_triv

/-- The pocket reads the word along the inverse of the boundary cycle of the complement. -/
theorem diagram_boundaryWord (P : PocketRegion Delta) :
    P.diagram.boundaryWord =
      Embedded.dartWord Delta (Embedded.invDarts Delta P.outer.cycle) := by
  unfold diagram
  rw [DiscDiagram.ofPlanar_boundaryWord,
    replaceGRegionFaceBoundary_newFace_word Delta P.outside P.outer]
  exact (Embedded.dartWord_reverse_alpha Delta P.outer.cycle).symm

/-- A relator budget of the boundary of the pocket is one of the boundary word of the face
set. -/
theorem isRelatorProduct_inner_of_diagram (P : PocketRegion Delta) {R : Set G} {m : ℕ}
    (h : RelatorDefectBudget.IsRelatorProduct R m P.diagram.boundaryValue) :
    RelatorDefectBudget.IsRelatorProduct R m
      (RelLetter.listVal (Embedded.dartWord Delta P.inner.cycle)) := by
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  have hword : P.diagram.boundaryWord = (Embedded.dartWord Delta P.inner.cycle).rotate k := by
    rw [P.diagram_boundaryWord, hk]
    exact List.map_rotate Delta.label P.inner.cycle k
  have h' : RelatorDefectBudget.IsRelatorProduct R m
      (RelLetter.listVal ((Embedded.dartWord Delta P.inner.cycle).rotate k)) := by
    rw [← hword]
    exact h
  exact isRelatorProduct_listVal_of_rotate _ k h'

open scoped Classical in
/-- The pocket has at most as many relator cells as `Δ` has inside the face set. -/
theorem diagram_rCellCount_le (P : PocketRegion Delta) :
    P.diagram.rCellCount ≤ (Delta.relatorCells.filter (fun C => C.face ∈ P.faces)).length := by
  unfold diagram
  rw [DiscDiagram.ofPlanar_rCellCount]
  unfold cellFaces
  exact (List.toFinset_card_le _).trans (by simp)

/-- **The pocket of a least-area diagram is least area.**  A shorter filling of the boundary
of the pocket fills the boundary word of the face set, and so bounds the relator cells of `Δ`
inside it (`DiscDiagram.LeastArea.length_filter_mem_le`). -/
theorem diagram_leastArea (P : PocketRegion Delta) (hlea : Delta.LeastArea) :
    P.diagram.LeastArea := by
  intro m hm
  exact P.diagram_rCellCount_le.trans
    (hlea.length_filter_mem_le P.faces P.inner P.outerFace_not_mem
      (P.isRelatorProduct_inner_of_diagram hm))

open scoped Classical in
/-- A relator cell of `Δ` inside the face set gives a relator cell of the pocket. -/
theorem diagram_rCellCount_pos (P : PocketRegion Delta)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells)
    (hCf : C.face ∈ P.faces) : 0 < P.diagram.rCellCount := by
  unfold diagram
  rw [DiscDiagram.ofPlanar_rCellCount, Finset.card_pos]
  refine ⟨keptFace Delta.toCombMap P.outside P.outer C.face (P.not_mem_outside hCf), ?_⟩
  unfold cellFaces
  rw [List.mem_toFinset]
  exact List.mem_map.mpr
    ⟨C, List.mem_filter.mpr ⟨hC, by simpa using hCf⟩, dif_neg (P.not_mem_outside hCf)⟩

open scoped Classical in
/-- A relator cell of `Δ` outside the face set gives fewer relator cells in the pocket than
in `Δ`. -/
theorem diagram_rCellCount_lt (P : PocketRegion Delta)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells)
    (hCf : C.face ∉ P.faces) : P.diagram.rCellCount < Delta.rCellCount := by
  have hpos : 0 < (Delta.relatorCells.filter (fun C => C.face ∉ P.faces)).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hC, by simpa using hCf⟩)
  have hsplit : Delta.relatorCells.length =
      (Delta.relatorCells.filter (fun C => C.face ∈ P.faces)).length +
        (Delta.relatorCells.filter (fun C => C.face ∉ P.faces)).length := by
    rw [List.length_eq_length_filter_add (l := Delta.relatorCells)
      (fun C => decide (C.face ∈ P.faces))]
    simp only [decide_not]
  have hle := P.diagram_rCellCount_le
  show P.diagram.rCellCount < Delta.relatorCells.length
  omega

/-- **The least-area pocket cut.**  The pocket of a least-area diagram with a relator cell
inside the face set and one outside is least area, and has at least one and fewer relator
cells than `Δ`. -/
theorem diagram_leastAreaCut (P : PocketRegion Delta) (hlea : Delta.LeastArea)
    {C C' : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hC : C ∈ Delta.relatorCells) (hCf : C.face ∈ P.faces)
    (hC' : C' ∈ Delta.relatorCells) (hC'f : C'.face ∉ P.faces) :
    P.diagram.LeastArea ∧ 0 < P.diagram.rCellCount ∧
      P.diagram.rCellCount < Delta.rCellCount :=
  ⟨P.diagram_leastArea hlea, P.diagram_rCellCount_pos hC hCf, P.diagram_rCellCount_lt hC' hC'f⟩

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.isRelatorProduct_listVal_of_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.cellFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_boundaryWord
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.isRelatorProduct_inner_of_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_rCellCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_leastArea
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_rCellCount_pos
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_rCellCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_leastAreaCut
