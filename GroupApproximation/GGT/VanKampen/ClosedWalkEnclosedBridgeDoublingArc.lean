import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTouchCornerStep
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling the bridges of a walk that is an arc of one relator cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.4.  The pocket of a same-face bridge dart of a relator
cell `i` is enclosed by its pocket walk, which is an arc of cell `i`.  The loop cut of that pocket reads
the pocket as a pocket region with the arc as its complement cycle, so every bridge of the walk has to
be doubled while the walk stays an arc of the cell.

* `darts_map_image_cellArc` and `darts_map_image_cellArc_spur`: one doubling maps an arc of any relator
  cell to the transported arc of the transported cell.  In the doubled face the dart map is `dartImage`,
  which is `image` (`image_eq_dartImage`); on any other cell `image` is the embedding, since no dart of
  another face is the doubled one.
* `ArcDoublingOutput`, `arcDoublingOutput`: the induction on the number of bridge darts for a walk that
  is an arc of a relator cell outside the enclosed faces.  Every walk dart lies on that cell, which is
  not the exterior, so only the inner-face doubling occurs.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv SimpleClosedWalkSides EdgeInsertion Embedded

namespace EnclosedBridgeDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A dart of an arc of a relator cell lies on the carrier of the cell. -/
theorem mem_cellDarts_of_mem_darts {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (A : CyclicArc (cellDarts Delta i)) {z : Delta.toCombMap.Dart} (hz : z ∈ A.darts) :
    z ∈ cellDarts Delta i := by
  have h1 : z ∈ A.rotated := List.mem_of_mem_take hz
  rcases List.mem_append.mp h1 with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

/-- A dart of an arc of a relator cell lies on the face of the cell. -/
theorem faceOf_of_mem_darts {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (A : CyclicArc (cellDarts Delta i)) {z : Delta.toCombMap.Dart} (hz : z ∈ A.darts) :
    Delta.toCombMap.faceOf z = (cell Delta i).face :=
  ((Delta.faceBoundary (cell Delta i).face).mem_iff z).mp (mem_cellDarts_of_mem_darts A hz)

section Inner

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **One doubling maps an arc of a relator cell to the transported arc**, in the inner-face
branch. -/
theorem darts_map_image_cellArc (i : Fin Delta.rCellCount) (A : CyclicArc (cellDarts Delta i)) :
    A.darts.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) =
      (A.mapTo (FaceEdgeDoubling.carrierImage Delta f j hlen hf (cell Delta i).face)
        (FaceEdgeDoubling.cellDarts_eq Delta f j hlen hf i)).darts := by
  rw [CyclicArc.mapTo_darts]
  refine List.map_congr_left fun z hz => ?_
  by_cases hface : (cell Delta i).face = f
  · rw [image_eq_dartImage Delta f j hlen z, hface, FaceEdgeDoubling.carrierImage_self]
  · have hz' : z ≠ FaceEdgeDoubling.dart Delta f j := fun h =>
      hface ((faceOf_of_mem_darts A hz).symm.trans
        (h ▸ FaceEdgeDoubling.dart_face Delta f j))
    rw [FaceEdgeDoubling.carrierImage_of_ne_dart Delta f j hlen hf _ hz', image_of_ne hz']
    rfl

end Inner

section Spur

variable (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- **One doubling maps an arc of a relator cell to the transported arc**, in the exterior
branch. -/
theorem darts_map_image_cellArc_spur (i : Fin Delta.rCellCount) (A : CyclicArc (cellDarts Delta i)) :
    A.darts.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta Delta.outerFace j)) =
      (A.mapTo (OuterSpurThickening.embedding Delta j hlen).darts
        (OuterSpurThickening.cellDarts_eq Delta j hlen i)).darts := by
  rw [CyclicArc.mapTo_darts]
  refine List.map_congr_left fun z hz => ?_
  have hz' : z ≠ FaceEdgeDoubling.dart Delta Delta.outerFace j := fun h =>
    (cell Delta i).face_ne_outer ((faceOf_of_mem_darts A hz).symm.trans
      (h ▸ FaceEdgeDoubling.dart_face Delta Delta.outerFace j))
  rw [image_of_ne hz']
  rfl

end Spur

open scoped Classical in
/-- **The doubling output for an arc walk**: an O-equivalent copy with a bridge-free enclosed face set
turning to its successor, whose walk is an arc of a relator cell outside the enclosed faces, with a
word-preserving correspondence of relator cells matching the enclosed ones. -/
def ArcDoublingOutput (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face) : Prop :=
  ∃ (Delta' : DiscDiagram.{u, w, v} W) (faces' : Finset Delta'.toCombMap.Face)
    (i' : Fin Delta'.rCellCount) (A' : CyclicArc (cellDarts Delta' i')),
    Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
    EnclosedFaceSetSucc Delta' faces' A'.darts ∧
    (∀ d ∈ A'.darts, Delta'.toCombMap.alpha d ∉ A'.darts) ∧
    (cell Delta' i').face ∉ faces' ∧
    ∃ e : Fin Delta.rCellCount ≃ Fin Delta'.rCellCount, ∀ k,
      (cell Delta' (e k)).word = (cell Delta k).word ∧
        ((cell Delta' (e k)).face ∈ faces' ↔ (cell Delta k).face ∈ faces)

open scoped Classical in
/-- **Doubling the bridges of an arc walk**, by strong induction on their number. -/
theorem arcDoublingOutput (n : ℕ) :
    ∀ (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
      (i : Fin Delta.rCellCount) (A : CyclicArc (cellDarts Delta i)),
      bridgeCount A.darts = n → EnclosedFaceSetSucc Delta faces A.darts →
      (cell Delta i).face ∉ faces → ArcDoublingOutput Delta faces := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Delta faces i A hn E hi
  by_cases hfree : ∀ d ∈ A.darts, Delta.toCombMap.alpha d ∉ A.darts
  · exact ⟨Delta, faces, i, A, ⟨OEquivalentDiscDiagram.refl Delta⟩, E, hfree, hi,
      Equiv.refl _, fun _ => ⟨rfl, Iff.rfl⟩⟩
  obtain ⟨d, hd, had⟩ : ∃ d ∈ A.darts, Delta.toCombMap.alpha d ∈ A.darts := by
    by_contra h
    exact hfree fun d hd had => h ⟨d, hd, had⟩
  have hdface := faceOf_of_mem_darts A hd
  have hlen : 1 < (Delta.faceBoundary (cell Delta i).face).darts.length := by
    rw [← hdface]
    exact one_lt_faceBoundary_length_of_bridge E hd had
  have hf : (cell Delta i).face ≠ Delta.outerFace := (cell Delta i).face_ne_outer
  obtain ⟨j, hj⟩ := exists_index_eq_dart Delta (cell Delta i).face (mem_cellDarts_of_mem_darts A hd)
  rw [← hj] at hd had
  have E' := enclosedFaceSetSucc_diagram Delta (cell Delta i).face j hlen hf E hd had
  have hlt := lt_of_lt_of_eq (bridgeCount_image_lt Delta (cell Delta i).face j hlen hd had) hn
  have hw := darts_map_image_cellArc Delta (cell Delta i).face j hlen hf i A
  have E'' : EnclosedFaceSetSucc (FaceEdgeDoubling.diagram Delta (cell Delta i).face j hlen hf)
      (newFaces Delta (cell Delta i).face j hlen faces)
      (A.mapTo (FaceEdgeDoubling.carrierImage Delta (cell Delta i).face j hlen hf (cell Delta i).face)
        (FaceEdgeDoubling.cellDarts_eq Delta (cell Delta i).face j hlen hf i)).darts := by
    rw [← hw]
    exact E'
  have hlt' : bridgeCount (M := (FaceEdgeDoubling.diagram Delta (cell Delta i).face j hlen hf).toCombMap)
      (A.mapTo (FaceEdgeDoubling.carrierImage Delta (cell Delta i).face j hlen hf (cell Delta i).face)
        (FaceEdgeDoubling.cellDarts_eq Delta (cell Delta i).face j hlen hf i)).darts < n := by
    rw [← hw]
    exact hlt
  have hi' : (cell (FaceEdgeDoubling.diagram Delta (cell Delta i).face j hlen hf)
      ((FaceEdgeDoubling.cellMap Delta (cell Delta i).face j hlen hf).indexEquiv i)).face ∉
        newFaces Delta (cell Delta i).face j hlen faces := by
    rw [PocketTouchCorner.cell_indexEquiv_face Delta (cell Delta i).face j hlen hf i]
    exact fun h => hi ((faceImage_mem_newFaces_iff Delta (cell Delta i).face j hlen faces _).mp h)
  obtain ⟨Delta'', faces'', i'', A'', ⟨equiv''⟩, E'', hfree'', hi'', e'', he''⟩ :=
    ih _ hlt' (FaceEdgeDoubling.diagram Delta (cell Delta i).face j hlen hf) _ _ _ rfl E'' hi'
  obtain ⟨e₁, he₁⟩ := cellCorrespondence_map (Delta := Delta)
    (Delta' := FaceEdgeDoubling.diagram Delta (cell Delta i).face j hlen hf)
    (faces := faces) (faces' := newFaces Delta (cell Delta i).face j hlen faces)
    (FaceEdgeDoubling.cell Delta (cell Delta i).face j hlen hf) rfl (fun _ => rfl)
    (fun C => faceImage_mem_newFaces_iff Delta (cell Delta i).face j hlen faces C.face)
  exact ⟨Delta'', faces'', i'', A'',
    ⟨(FaceEdgeDoubling.oEquivalent Delta (cell Delta i).face j hlen hf).trans equiv''⟩, E'', hfree'',
    hi'', e₁.trans e'', fun k => ⟨(he'' (e₁ k)).1.trans (he₁ k).1, (he'' (e₁ k)).2.trans (he₁ k).2⟩⟩

end EnclosedBridgeDoubling

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling

#audit_axioms mem_cellDarts_of_mem_darts
#audit_axioms faceOf_of_mem_darts
#audit_axioms darts_map_image_cellArc
#audit_axioms darts_map_image_cellArc_spur
#audit_axioms arcDoublingOutput
