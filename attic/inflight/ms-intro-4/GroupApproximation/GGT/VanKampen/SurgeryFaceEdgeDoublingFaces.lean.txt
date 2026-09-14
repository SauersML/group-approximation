import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.Meta.AxiomGuard

/-!
# Faces of the doubled diagram, and counting bad corners

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch step for a pocket in first-turn order splits a vertex at two
corners inside the pocket, and needs good corners: no boundary dart on a relator face, and distinct
boundary darts on distinct faces.  A doubling of an edge (`FaceEdgeDoubling.diagram`) at a bad
boundary dart moves that dart onto the new digon.  This module collects the map-level facts both the
cell and the section versions of that reduction use.

* `FaceEdgeDoubling.faceOf_diagram_embed_dart`: the doubled dart lies on the digon.
* `FaceEdgeDoubling.faceOf_diagram_embed_of_ne`: every other old dart lies on the image of its face.
* `FaceEdgeDoubling.exists_relatorCell_of_mem_diagram`: every relator face of the doubled diagram is
  the image of an old relator face.
* `CornerCount.one_lt_length_of_relatorCell`: with relator words longer than one letter, a relator
  face has more than one dart, so the doubling applies to it.
* `CornerCount.one_lt_length_of_mem_ne`, `CornerCount.countP_lt_countP_of_imp`: the list facts behind
  the induction on the number of bad corners.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace CornerCount

/-- **A strictly smaller count.**  If `q` implies `p` along a list, and some entry satisfies `p` but
not `q`, then fewer entries satisfy `q` than `p`. -/
theorem countP_lt_countP_of_imp {α : Type*} {p q : α → Bool} {l : List α}
    (himp : ∀ x ∈ l, q x = true → p x = true) (hex : ∃ x ∈ l, p x = true ∧ q x = false) :
    l.countP q < l.countP p := by
  induction l with
  | nil =>
      obtain ⟨x, hx, -⟩ := hex
      exact absurd hx (by simp)
  | cons a l ih =>
      have himp' : ∀ y ∈ l, q y = true → p y = true :=
        fun y hy => himp y (List.mem_cons_of_mem a hy)
      obtain ⟨x, hx, hpx, hqx⟩ := hex
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hle : l.countP q ≤ l.countP p := List.countP_mono_left himp'
        rw [List.countP_cons_of_pos hpx, List.countP_cons_of_neg (by simp [hqx])]
        omega
      · have hlt := ih himp' ⟨x, hx', hpx, hqx⟩
        by_cases hqa : q a = true
        · rw [List.countP_cons_of_pos hqa,
            List.countP_cons_of_pos (himp a List.mem_cons_self hqa)]
          omega
        · rw [List.countP_cons_of_neg hqa]
          by_cases hpa : p a = true
          · rw [List.countP_cons_of_pos hpa]
            omega
          · rw [List.countP_cons_of_neg hpa]
            exact hlt

/-- A list with two distinct entries has length more than one. -/
theorem one_lt_length_of_mem_ne {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 1 < l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact absurd ha (by simp)
  · rw [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · simp only [List.length_cons]
    omega

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A relator face with a long word has more than one dart.** -/
theorem one_lt_length_of_relatorCell (Delta : DiscDiagram.{u, w, v} W)
    (hW : ∀ word ∈ W, 1 < word.length)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells) :
    1 < (Delta.faceBoundary C.face).darts.length := by
  have h := congrArg List.length (Delta.relatorCell_word C hC)
  rw [List.length_map] at h
  rw [← h]
  exact hW C.word C.word_mem

end CornerCount

namespace FaceEdgeDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **The doubled dart lies on the digon.** -/
theorem faceOf_diagram_embed_dart :
    (diagram Delta f j hlen hf).toCombMap.faceOf
        ((embedding Delta f j hlen hf).darts (dart Delta f j)) =
      digon Delta f j hlen :=
  faceOf_embed_dart_digon Delta f j hlen

/-- **Every other old dart lies on the image of its face.** -/
theorem faceOf_diagram_embed_of_ne {e : Delta.toCombMap.Dart} (hne : e ≠ dart Delta f j) :
    (diagram Delta f j hlen hf).toCombMap.faceOf ((embedding Delta f j hlen hf).darts e) =
      faceImage Delta f j hlen (Delta.toCombMap.faceOf e) := by
  by_cases he : Delta.toCombMap.faceOf e = f
  · rw [he, faceImage_self]
    exact faceOf_embed_of_face_of_ne Delta f j hlen he hne
  · exact faceOf_embed_of_face_ne Delta f j hlen he

/-- **Every relator face of the doubled diagram is the image of an old relator face.** -/
theorem exists_relatorCell_of_mem_diagram
    {C : RelatorCell (diagram Delta f j hlen hf).toCombMap (diagram Delta f j hlen hf).outerFace W}
    (hC : C ∈ (diagram Delta f j hlen hf).relatorCells) :
    ∃ C₀ ∈ Delta.relatorCells, C.face = faceImage Delta f j hlen C₀.face := by
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact ⟨C₀, hC₀, rfl⟩

end FaceEdgeDoubling

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CornerCount.countP_lt_countP_of_imp
#audit_axioms GroupApproximation.GGT.VanKampen.CornerCount.one_lt_length_of_mem_ne
#audit_axioms GroupApproximation.GGT.VanKampen.CornerCount.one_lt_length_of_relatorCell
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.faceOf_diagram_embed_dart
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.faceOf_diagram_embed_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.exists_relatorCell_of_mem_diagram
