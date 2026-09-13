import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchCarry
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set across the doubling of an edge inside it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A vertex splitting inside a pinched pocket face set
(`PocketFaceSet.exists_pinchStep_of_inside`) merges two corners of the face set, and both must be
G-faces.  When a corner lies in a relator face `f` of the face set, the doubling of an edge of `f`
(`FaceEdgeDoubling.diagram`) puts a G-cell digon in that corner.  The new face set holds the image
faces and the digon (`FaceEdgeDoubling.collarFaceSet`), so its boundary darts are the old ones and
the pocket face set transports by the dart embedding, with the same walk order and the same repeated
visits.

* `FaceEdgeDoubling.collarBoundaryCycle`: the boundary cycle of a face set holding the doubled face,
  mapped by the dart embedding.
* `PocketFaceSet.faceEdgeDoublingInside`: the transported pocket face set.
* `PocketFaceSet.faceEdgeDoublingInside_closedWalk` and `faceEdgeDoublingInside_repeatedVisits`:
  walk order and repeated visits are unchanged.
* `PocketFaceSet.exists_pinchStep_of_faceEdgeDoublingInside`: the conclusion of
  `exists_pinchStep_of_inside` for a split of the doubled diagram, back on the old diagram.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace FaceEdgeDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **The boundary cycle of a face set holding the doubled face, after the doubling**: the old
cycle, mapped by the dart embedding. -/
noncomputable def collarBoundaryCycle {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap S) :
    Surgery.MapCollapse.BoundaryCycle (diagram Delta f j hlen hf).toCombMap
      (collarFaceSet Delta f j hlen S) where
  cycle := B.cycle.map (embedding Delta f j hlen hf).darts
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := B.cycle_nodup.map (embedding Delta f j hlen hf).darts.injective
  cycle_mem_iff x :=
    (isBoundaryDart_collarFaceSet_iff Delta f j hlen hS (fun e => (B.cycle_mem_iff e).symm) x).symm

theorem collarBoundaryCycle_cycle {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap S) :
    (collarBoundaryCycle Delta f j hlen hf hS B).cycle =
      B.cycle.map (embedding Delta f j hlen hf).darts :=
  rfl

end FaceEdgeDoubling

namespace PocketFaceSet

open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The source cell lies outside every face of the face set. -/
theorem source_face_ne (K : PocketFaceSet D eps X lo hi) {f : X.toCombMap.Face}
    (hs : f ∈ K.faces) : (Embedded.cell X K.source).face ≠ f :=
  fun h => K.source_not_mem (by rw [h]; exact hs)

/-- **The pocket face set across the doubling of an edge** of a face `f` inside the face set: the
image faces with the new digon, the same cells, and the boundary cycle, the arcs and the sides
mapped by the dart embedding. -/
noncomputable def faceEdgeDoublingInside (K : PocketFaceSet D eps X lo hi)
    (f : X.toCombMap.Face) (j : Fin (X.faceBoundary f).darts.length)
    (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace) (hs : f ∈ K.faces) :
    PocketFaceSet D eps (FaceEdgeDoubling.diagram X f j hlen hf) lo hi where
  faces := FaceEdgeDoubling.collarFaceSet X f j hlen K.faces
  outerFace_not_mem :=
    FaceEdgeDoubling.outerFace_not_mem_collarFaceSet X f j hlen hf K.outerFace_not_mem
  source := (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv K.source
  source_not_mem := by
    rw [(FaceEdgeDoubling.cellMap X f j hlen hf).indexed_cell K.source,
      (FaceEdgeDoubling.cellMap X f j hlen hf).face_eq]
    exact fun h => K.source_not_mem
      ((FaceEdgeDoubling.mem_collarFaceSet_faceImage X f j hlen K.faces _).mp h)
  kept := (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv K.kept
  kept_mem := by
    rw [(FaceEdgeDoubling.cellMap X f j hlen hf).indexed_cell K.kept,
      (FaceEdgeDoubling.cellMap X f j hlen hf).face_eq]
    exact (FaceEdgeDoubling.mem_collarFaceSet_faceImage X f j hlen K.faces _).mpr K.kept_mem
  sourceArc := K.sourceArc.mapTo
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X K.source).face)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf K.source)
  targetArc := K.targetArc.mapTo (FaceEdgeDoubling.embedding X f j hlen hf).darts
    ((FaceEdgeDoubling.embedding X f j hlen hf).outerDarts_eq hf)
  firstSide := K.firstSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts
  secondSide := K.secondSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts
  boundary := FaceEdgeDoubling.collarBoundaryCycle X f j hlen hf hs K.boundary
  decomposition := by
    have hsa : (K.sourceArc.mapTo
        (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X K.source).face)
        (FaceEdgeDoubling.cellDarts_eq X f j hlen hf K.source)).darts =
          K.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
      (CyclicArc.mapTo_darts K.sourceArc
        (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X K.source).face)
        (FaceEdgeDoubling.cellDarts_eq X f j hlen hf K.source)).trans
        (congrArg (fun φ => K.sourceArc.darts.map φ)
          (FaceEdgeDoubling.carrierImage_of_ne X f j hlen hf (K.source_face_ne hs)))
    rw [hsa, CyclicArc.mapTo_darts, DiscEmbeddingAway.invDarts_map,
      FaceEdgeDoubling.collarBoundaryCycle_cycle, K.decomposition]
    simp only [List.map_append]
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
  lo_le := by
    rw [CyclicArc.mapTo_start]
    exact K.lo_le
  le_hi := by
    rw [CyclicArc.mapTo_start, CyclicArc.mapTo_length]
    exact K.le_hi

variable (K : PocketFaceSet D eps X lo hi) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace) (hs : f ∈ K.faces)

theorem faceEdgeDoublingInside_faces :
    (K.faceEdgeDoublingInside f j hlen hf hs).faces =
      FaceEdgeDoubling.collarFaceSet X f j hlen K.faces :=
  rfl

theorem faceEdgeDoublingInside_boundary_cycle :
    (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle =
      K.boundary.cycle.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  rfl

/-- **The doubling keeps walk order.** -/
theorem faceEdgeDoublingInside_closedWalk (hK : K.ClosedWalk) :
    (K.faceEdgeDoublingInside f j hlen hf hs).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (FaceEdgeDoubling.embedding X f j hlen hf).darts).IsChain
      (fun d e => (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha d) =
          (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f j hlen hf d e).mpr h)
  · change (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f j hlen hf).darts).getLast
            (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty)) =
      (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf
        ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f j hlen hf).darts).head
          (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f j hlen hf _ _).mpr hK.2

/-- **The doubling keeps the repeated visits.** -/
theorem faceEdgeDoublingInside_repeatedVisits :
    (K.faceEdgeDoublingInside f j hlen hf hs).repeatedVisits = K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  rw [faceEdgeDoublingInside_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf ∘
      (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    X.toCombMap.vertexOf
    (fun a b => FaceEdgeDoubling.vertexOf_embedding_eq_iff X f j hlen hf a b) _

/-- **A pinch step through the doubling of an edge inside the face set.**  A vertex splitting of
the doubled diagram inside the transported face set, with turns along vertex rotation and two
boundary darts on the new vertices, gives the conclusion of `exists_pinchStep_of_inside` for the
old diagram. -/
theorem exists_pinchStep_of_faceEdgeDoublingInside
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (I : PinchSplit.Input (FaceEdgeDoubling.diagram X f j hlen hf))
    (hI : I.Inside (K.faceEdgeDoublingInside f j hlen hf hs).faces)
    (hchain : (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.IsChain fun d e =>
      I.StretchAvoids ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha d) e ∨
        I.StretchAvoids e ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha d))
    (hcloses :
      I.StretchAvoids ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.getLast
            (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty))
          ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.head
            (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty) ∨
        I.StretchAvoids ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.head
            (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty)
          ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
            ((K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle.getLast
              (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle_nonempty)))
    {e₁ e₂ : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Dart}
    (he₁ : e₁ ∈ (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle)
    (he₂ : e₂ ∈ (K.faceEdgeDoublingInside f j hlen hf hs).boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨X', K', ⟨hequiv⟩, hlabel', hwalk, hlt⟩ :=
    (K.faceEdgeDoublingInside f j hlen hf hs).exists_pinchStep_of_inside
      (FaceEdgeDoubling.label_letter X f j hlen hf hlabel) I hI hchain hcloses he₁ he₂ hx hy
  exact ⟨X', K', ⟨(FaceEdgeDoubling.oEquivalent X f j hlen hf).trans hequiv⟩, hlabel', hwalk,
    lt_of_lt_of_eq hlt (K.faceEdgeDoublingInside_repeatedVisits f j hlen hf hs)⟩

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.collarBoundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.source_face_ne
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoublingInside
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoublingInside_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoublingInside_repeatedVisits
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_pinchStep_of_faceEdgeDoublingInside
