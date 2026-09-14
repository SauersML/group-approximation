import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening the pocket corners at a touch vertex

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`: the X-pocket walk
`invDarts X ++ invDarts B` touches itself at a vertex `v` where the face part meets the cell part
(`OsinLemma94CaseOneTouchOnlyStatement`).  At `v` the walk has two passages `in₁ → out₁` and
`in₂ → out₂`, and the vertex split separating them cuts at `alpha in₁` and `alpha in₂`.  It merges
the faces `faceOf in₁` and `faceOf in₂`, which lie on the side of the walk.  `PinchSplit.Input`
needs them to be distinct G-faces.

This module doubles an edge of each corner face along its in-dart (`FaceEdgeDoubling.diagram`).  The
in-dart then lies on a new G-cell digon, which is neither the exterior nor a relator face.  The
doubling keeps every old dart, label and vertex.

* `one_lt_faceBoundary_length_of_not_loop`: a dart that is not a loop lies on a face with at least
  two darts, so its edge can be doubled.
* `exists_dart_eq`: the index of a dart in the traversal of its face.
* `faceOf_embedding_doubled`, `digon_ne_outerFace`, `digon_not_cell`: the doubled dart lies on a
  G-cell digon off the exterior.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PocketTouchCorner

open EdgeInsertion

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Any two entries of a list with at most one entry are equal. -/
theorem eq_of_mem_of_length_le_one {α : Type*} :
    ∀ (l : List α), l.length ≤ 1 → ∀ a ∈ l, ∀ b ∈ l, a = b
  | [], _, a, ha, _, _ => by simp at ha
  | [_], _, a, ha, b, hb => by
      simp only [List.mem_singleton] at ha hb
      rw [ha, hb]
  | _ :: _ :: _, hl, _, _, _, _ => by
      simp only [List.length_cons] at hl
      omega

/-- **A dart that is not a loop lies on a face with at least two darts.**  A face with one dart
`d` has `sigma (alpha d) = d`, so `d` and `alpha d` start at one vertex. -/
theorem one_lt_faceBoundary_length_of_not_loop {Delta : DiscDiagram.{u, w, v} W}
    {d : Delta.toCombMap.Dart}
    (hloop : Delta.toCombMap.vertexOf d ≠ Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d)) :
    1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length := by
  by_contra hle
  have hle' : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length ≤ 1 := by omega
  have hmem : d ∈ (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts :=
    ((Delta.faceBoundary (Delta.toCombMap.faceOf d)).mem_iff d).mpr rfl
  have hface : Delta.toCombMap.faceOf (Delta.toCombMap.facePerm d) =
      Delta.toCombMap.faceOf d :=
    ((Delta.toCombMap.faceOf_eq_iff d (Delta.toCombMap.facePerm d)).mpr
      ⟨1, by rw [zpow_one]⟩).symm
  have hmem' : Delta.toCombMap.facePerm d ∈ (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts :=
    ((Delta.faceBoundary (Delta.toCombMap.faceOf d)).mem_iff _).mpr hface
  have hfix : Delta.toCombMap.facePerm d = d :=
    eq_of_mem_of_length_le_one _ hle' _ hmem' _ hmem
  have hsig : Delta.toCombMap.sigma (Delta.toCombMap.alpha d) = d := by
    unfold CombMap.facePerm at hfix
    rwa [Equiv.Perm.mul_apply] at hfix
  exact hloop ((Delta.toCombMap.vertexOf_eq_iff _ _).mpr ⟨1, by rw [zpow_one]; exact hsig⟩).symm

/-- The index of a dart in the traversal of its face. -/
theorem exists_dart_eq (Delta : DiscDiagram.{u, w, v} W) (d : Delta.toCombMap.Dart) :
    ∃ j : Fin (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length,
      FaceEdgeDoubling.dart Delta (Delta.toCombMap.faceOf d) j = d := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp
    (((Delta.faceBoundary (Delta.toCombMap.faceOf d)).mem_iff d).mpr rfl)
  exact ⟨n, (FaceEdgeDoubling.dart_eq_get Delta _ n).trans hn⟩

section Doubling

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **The doubled dart lies on the digon.** -/
theorem faceOf_embedding_doubled {d : Delta.toCombMap.Dart}
    (hj : FaceEdgeDoubling.dart Delta f j = d) :
    (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.faceOf
        ((FaceEdgeDoubling.embedding Delta f j hlen hf).darts d) =
      FaceEdgeDoubling.digon Delta f j hlen := by
  subst hj
  exact FaceEdgeDoubling.faceOf_embed_dart_digon Delta f j hlen

/-- **The digon is not the exterior.** -/
theorem digon_ne_outerFace :
    FaceEdgeDoubling.digon Delta f j hlen ≠ (FaceEdgeDoubling.diagram Delta f j hlen hf).outerFace :=
  fun h => FaceEdgeDoubling.keep_ne_digon Delta f j hlen hf.symm h.symm

/-- **The digon is not a relator face.** -/
theorem digon_not_cell :
    ∀ C ∈ (FaceEdgeDoubling.diagram Delta f j hlen hf).relatorCells,
      C.face ≠ FaceEdgeDoubling.digon Delta f j hlen := by
  intro C hC
  obtain ⟨C₀, -, rfl⟩ := List.mem_map.mp hC
  exact FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen C₀.face

end Doubling

end GroupApproximation.GGT.VanKampen.PocketTouchCorner

#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.eq_of_mem_of_length_le_one
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.one_lt_faceBoundary_length_of_not_loop
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.exists_dart_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.faceOf_embedding_doubled
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.digon_ne_outerFace
#audit_axioms GroupApproximation.GGT.VanKampen.PocketTouchCorner.digon_not_cell
