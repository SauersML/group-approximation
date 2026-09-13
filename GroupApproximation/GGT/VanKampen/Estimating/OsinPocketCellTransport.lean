import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingInside
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket between two cells across the doubling of an edge

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

The cell analogues of `PocketFaceSet.faceEdgeDoubling` (lane hull-respell,
`Estimating/OsinPocketEdgeDoubling.lean`) and `PocketFaceSet.faceEdgeDoublingInside` (lane
ghw-assembly, `Estimating/OsinPocketEdgeDoublingInside.lean`), over the same map-level layer: the
dart embedding `FaceEdgeDoubling.embedding`, the cell map `FaceEdgeDoubling.cellMap`, and the
carrier images of the cells.  These are the corner fixes of the cell pinch step
(`CellPocketPinchStepPosStatement`, `Estimating/OsinPocketCellPinchStep.lean`).

* `CellPocketFaceSet.faceEdgeDoubling`: across the doubling of an edge of a face outside the face
  set, when neither arc holds the doubled dart.  The face set, both cells, the kept cell, the arcs,
  the sides and the boundary cycle are mapped by the embedding.
* `CellPocketFaceSet.faceEdgeDoublingInside`: across the doubling of an edge of a face inside the
  face set, which gains the new digon.  Both cells lie outside the face set, so both arcs avoid the
  doubled face.
* Both keep walk order (`_closedWalk`) and the repeated visits (`_repeatedVisits`), and map the
  boundary cycle by the embedding (`_boundary_cycle`), so first-turn order is carried by
  `EdgeInsertion.firstTurnChain_map_embed` (`Estimating/OsinPocketEdgeDoublingFirstTurns.lean`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The first cell lies outside every face of the face set. -/
theorem first_face_ne (K : CellPocketFaceSet D eps X i j) {f : X.toCombMap.Face}
    (hs : f ∈ K.faces) : (Embedded.cell X i).face ≠ f :=
  fun h => K.first_not_mem (by rw [h]; exact hs)

/-- The second cell lies outside every face of the face set. -/
theorem second_face_ne (K : CellPocketFaceSet D eps X i j) {f : X.toCombMap.Face}
    (hs : f ∈ K.faces) : (Embedded.cell X j).face ≠ f :=
  fun h => K.second_not_mem (by rw [h]; exact hs)

/-- **The cell pocket face set across the doubling of an edge** of a face `f` outside the face set,
when neither arc holds the doubled dart: the image faces and cells, with the boundary cycle, the
arcs and the sides mapped by the dart embedding. -/
noncomputable def faceEdgeDoubling (K : CellPocketFaceSet D eps X i j) (f : X.toCombMap.Face)
    (k : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
    (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
    (hfirst : FaceEdgeDoubling.dart X f k ∉ K.firstArc.darts)
    (hsecond : FaceEdgeDoubling.dart X f k ∉ K.secondArc.darts) :
    CellPocketFaceSet D eps (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j) where
  faces := (FaceEdgeDoubling.embedding X f k hlen hf).faceSet K.faces
  outerFace_not_mem := by
    rw [(FaceEdgeDoubling.embedding X f k hlen hf).outer]
    exact fun h => K.outerFace_not_mem ((Finset.mem_map' _).mp h)
  first_not_mem := by
    rw [(FaceEdgeDoubling.cellMap X f k hlen hf).indexed_cell i,
      (FaceEdgeDoubling.cellMap X f k hlen hf).face_eq]
    exact fun h => K.first_not_mem
      ((FaceEdgeDoubling.faceImage_mem_faceSet_iff X f k hlen hf hs _).mp h)
  second_not_mem := by
    rw [(FaceEdgeDoubling.cellMap X f k hlen hf).indexed_cell j,
      (FaceEdgeDoubling.cellMap X f k hlen hf).face_eq]
    exact fun h => K.second_not_mem
      ((FaceEdgeDoubling.faceImage_mem_faceSet_iff X f k hlen hf hs _).mp h)
  kept := (FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv K.kept
  kept_mem := by
    rw [(FaceEdgeDoubling.cellMap X f k hlen hf).indexed_cell K.kept,
      (FaceEdgeDoubling.cellMap X f k hlen hf).face_eq]
    exact (FaceEdgeDoubling.faceImage_mem_faceSet_iff X f k hlen hf hs _).mpr K.kept_mem
  firstArc := K.firstArc.mapTo
    (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X i).face)
    (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)
  secondArc := K.secondArc.mapTo
    (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X j).face)
    (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)
  firstSide := K.firstSide.map (FaceEdgeDoubling.embedding X f k hlen hf).darts
  secondSide := K.secondSide.map (FaceEdgeDoubling.embedding X f k hlen hf).darts
  boundary := (FaceEdgeDoubling.embedding X f k hlen hf).boundaryCycle K.faces hs K.boundary
  decomposition := by
    have hfa : (K.firstArc.mapTo
        (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X i).face)
        (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)).darts =
          K.firstArc.darts.map (FaceEdgeDoubling.embedding X f k hlen hf).darts :=
      FaceEdgeDoubling.mapTo_darts_of_avoid X f k hlen hf K.firstArc _
        (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f k hlen hf
          (Embedded.cell X i).face hd) _ hfirst
    have hsa : (K.secondArc.mapTo
        (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X j).face)
        (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)).darts =
          K.secondArc.darts.map (FaceEdgeDoubling.embedding X f k hlen hf).darts :=
      FaceEdgeDoubling.mapTo_darts_of_avoid X f k hlen hf K.secondArc _
        (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f k hlen hf
          (Embedded.cell X j).face hd) _ hsecond
    rw [hfa, hsa, DiscEmbeddingAway.invDarts_map, DiscEmbeddingAway.invDarts_map,
      DiscEmbeddingAway.boundaryCycle_cycle, K.decomposition]
    simp only [List.map_append]
  firstArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.firstArc_pos
  secondArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.secondArc_pos
  firstSide_length_le := by
    rw [List.length_map]
    exact K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_map]
    exact K.secondSide_length_le
  firstSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.firstSide_norm_le
  secondSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.secondSide_norm_le

section Outside

variable (K : CellPocketFaceSet D eps X i j) (f : X.toCombMap.Face)
  (k : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
  (hfirst : FaceEdgeDoubling.dart X f k ∉ K.firstArc.darts)
  (hsecond : FaceEdgeDoubling.dart X f k ∉ K.secondArc.darts)

theorem faceEdgeDoubling_boundary_cycle :
    (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).boundary.cycle =
      K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts :=
  rfl

/-- **The doubling outside the face set keeps walk order.** -/
theorem faceEdgeDoubling_closedWalk (hK : K.ClosedWalk) :
    (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts).IsChain
      (fun d e => (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf
        ((FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.alpha d) =
          (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f k hlen hf d e).mpr h)
  · change (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf
        ((FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.alpha
          ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts).getLast
            (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).boundary.cycle_nonempty)) =
      (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf
        ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts).head
          (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f k hlen hf _ _).mpr hK.2

/-- **The doubling outside the face set keeps the repeated visits.** -/
theorem faceEdgeDoubling_repeatedVisits :
    (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).repeatedVisits = K.repeatedVisits := by
  unfold CellPocketFaceSet.repeatedVisits
  rw [faceEdgeDoubling_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf ∘
      (FaceEdgeDoubling.embedding X f k hlen hf).darts)
    X.toCombMap.vertexOf
    (fun a b => FaceEdgeDoubling.vertexOf_embedding_eq_iff X f k hlen hf a b) _

end Outside

/-- **The cell pocket face set across the doubling of an edge** of a face `f` inside the face set:
the image faces with the new digon, the same cells, and the boundary cycle, the arcs and the sides
mapped by the dart embedding. -/
noncomputable def faceEdgeDoublingInside (K : CellPocketFaceSet D eps X i j)
    (f : X.toCombMap.Face) (k : Fin (X.faceBoundary f).darts.length)
    (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace) (hs : f ∈ K.faces) :
    CellPocketFaceSet D eps (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j) where
  faces := FaceEdgeDoubling.collarFaceSet X f k hlen K.faces
  outerFace_not_mem :=
    FaceEdgeDoubling.outerFace_not_mem_collarFaceSet X f k hlen hf K.outerFace_not_mem
  first_not_mem := by
    rw [(FaceEdgeDoubling.cellMap X f k hlen hf).indexed_cell i,
      (FaceEdgeDoubling.cellMap X f k hlen hf).face_eq]
    exact fun h => K.first_not_mem
      ((FaceEdgeDoubling.mem_collarFaceSet_faceImage X f k hlen K.faces _).mp h)
  second_not_mem := by
    rw [(FaceEdgeDoubling.cellMap X f k hlen hf).indexed_cell j,
      (FaceEdgeDoubling.cellMap X f k hlen hf).face_eq]
    exact fun h => K.second_not_mem
      ((FaceEdgeDoubling.mem_collarFaceSet_faceImage X f k hlen K.faces _).mp h)
  kept := (FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv K.kept
  kept_mem := by
    rw [(FaceEdgeDoubling.cellMap X f k hlen hf).indexed_cell K.kept,
      (FaceEdgeDoubling.cellMap X f k hlen hf).face_eq]
    exact (FaceEdgeDoubling.mem_collarFaceSet_faceImage X f k hlen K.faces _).mpr K.kept_mem
  firstArc := K.firstArc.mapTo
    (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X i).face)
    (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)
  secondArc := K.secondArc.mapTo
    (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X j).face)
    (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)
  firstSide := K.firstSide.map (FaceEdgeDoubling.embedding X f k hlen hf).darts
  secondSide := K.secondSide.map (FaceEdgeDoubling.embedding X f k hlen hf).darts
  boundary := FaceEdgeDoubling.collarBoundaryCycle X f k hlen hf hs K.boundary
  decomposition := by
    have hfa : (K.firstArc.mapTo
        (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X i).face)
        (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)).darts =
          K.firstArc.darts.map (FaceEdgeDoubling.embedding X f k hlen hf).darts :=
      (CyclicArc.mapTo_darts K.firstArc
        (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X i).face)
        (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)).trans
        (congrArg (fun φ => K.firstArc.darts.map φ)
          (FaceEdgeDoubling.carrierImage_of_ne X f k hlen hf (K.first_face_ne hs)))
    have hsa : (K.secondArc.mapTo
        (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X j).face)
        (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)).darts =
          K.secondArc.darts.map (FaceEdgeDoubling.embedding X f k hlen hf).darts :=
      (CyclicArc.mapTo_darts K.secondArc
        (FaceEdgeDoubling.carrierImage X f k hlen hf (Embedded.cell X j).face)
        (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)).trans
        (congrArg (fun φ => K.secondArc.darts.map φ)
          (FaceEdgeDoubling.carrierImage_of_ne X f k hlen hf (K.second_face_ne hs)))
    rw [hfa, hsa, DiscEmbeddingAway.invDarts_map, DiscEmbeddingAway.invDarts_map,
      FaceEdgeDoubling.collarBoundaryCycle_cycle, K.decomposition]
    simp only [List.map_append]
  firstArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.firstArc_pos
  secondArc_pos := by
    rw [CyclicArc.mapTo_length]
    exact K.secondArc_pos
  firstSide_length_le := by
    rw [List.length_map]
    exact K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_map]
    exact K.secondSide_length_le
  firstSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.firstSide_norm_le
  secondSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.secondSide_norm_le

section Inside

variable (K : CellPocketFaceSet D eps X i j) (f : X.toCombMap.Face)
  (k : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace) (hs : f ∈ K.faces)

theorem faceEdgeDoublingInside_boundary_cycle :
    (K.faceEdgeDoublingInside f k hlen hf hs).boundary.cycle =
      K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts :=
  rfl

/-- **The doubling inside the face set keeps walk order.** -/
theorem faceEdgeDoublingInside_closedWalk (hK : K.ClosedWalk) :
    (K.faceEdgeDoublingInside f k hlen hf hs).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts).IsChain
      (fun d e => (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf
        ((FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.alpha d) =
          (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f k hlen hf d e).mpr h)
  · change (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf
        ((FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.alpha
          ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts).getLast
            (K.faceEdgeDoublingInside f k hlen hf hs).boundary.cycle_nonempty)) =
      (FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf
        ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f k hlen hf).darts).head
          (K.faceEdgeDoublingInside f k hlen hf hs).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f k hlen hf _ _).mpr hK.2

/-- **The doubling inside the face set keeps the repeated visits.** -/
theorem faceEdgeDoublingInside_repeatedVisits :
    (K.faceEdgeDoublingInside f k hlen hf hs).repeatedVisits = K.repeatedVisits := by
  unfold CellPocketFaceSet.repeatedVisits
  rw [faceEdgeDoublingInside_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((FaceEdgeDoubling.diagram X f k hlen hf).toCombMap.vertexOf ∘
      (FaceEdgeDoubling.embedding X f k hlen hf).darts)
    X.toCombMap.vertexOf
    (fun a b => FaceEdgeDoubling.vertexOf_embedding_eq_iff X f k hlen hf a b) _

end Inside

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoubling_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoubling_repeatedVisits
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoublingInside
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoublingInside_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoublingInside_repeatedVisits
