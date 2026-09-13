import GroupApproximation.GGT.VanKampen.SurgeryOuterSpurThickening
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set across the thickening of an outer spur

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pinched pocket face set passes twice through a vertex, and the
vertex splitting there needs both gap corners away from the exterior.  When a gap corner lies in
the exterior, thickening an outer edge `w_j` there (`OuterSpurThickening.diagram`) first fills
the corner with a G-cell digon.  The thickening keeps every old dart, label, vertex and relator
cell, and it reads the exterior traversal position by position, with the reverse of the new dart
in the place of `α w_j` (`OuterSpurThickening.outerDarts_eq`).  So when the target arc `t_2`
avoids `α w_j`, the pocket face set transports by the dart embedding, with the target arc at the
same start position and of the same length, the same walk order and the same repeated visits.

* `OuterSpurThickening.vertexOf_embedding_eq_iff`, `vertexOf_alpha_embedding_eq_iff` and
  `label_letter`: vertices and letter labels across the thickening.
* `OuterSpurThickening.outerArc_mapTo_darts`: an arc of the exterior traversal avoiding `α w_j`
  goes to its image under the dart embedding.
* `PocketFaceSet.alpha_outerSpurDart_not_mem_targetArc`: the target arc avoids `α w_j` when the
  face of `α w_j` is not in the face set.
* `PocketFaceSet.outerSpurThickening`: the transported pocket face set.
* `PocketFaceSet.outerSpurThickening_closedWalk` and `outerSpurThickening_repeatedVisits`: walk
  order and repeated visits are unchanged.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace OuterSpurThickening

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- **The thickening keeps the vertices of old darts.** -/
theorem vertexOf_embedding_eq_iff (x y : Delta.toCombMap.Dart) :
    (diagram Delta j hlen).toCombMap.vertexOf ((embedding Delta j hlen).darts x) =
        (diagram Delta j hlen).toCombMap.vertexOf ((embedding Delta j hlen).darts y) ↔
      Delta.toCombMap.vertexOf x = Delta.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff Delta.toCombMap
    (EdgeInsertion.firstCorner Delta.toCombMap
      (FaceEdgeDoubling.rebased Delta Delta.outerFace j))
    (EdgeInsertion.secondCorner Delta.toCombMap
      (FaceEdgeDoubling.rebased Delta Delta.outerFace j)
      (FaceEdgeDoubling.second Delta Delta.outerFace j hlen)) x y

/-- **The thickening keeps the vertices of old darts and their reverses.** -/
theorem vertexOf_alpha_embedding_eq_iff (x y : Delta.toCombMap.Dart) :
    (diagram Delta j hlen).toCombMap.vertexOf
        ((diagram Delta j hlen).toCombMap.alpha ((embedding Delta j hlen).darts x)) =
        (diagram Delta j hlen).toCombMap.vertexOf ((embedding Delta j hlen).darts y) ↔
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha x) = Delta.toCombMap.vertexOf y := by
  rw [(embedding Delta j hlen).alpha]
  exact vertexOf_embedding_eq_iff Delta j hlen _ y

/-- **The thickening keeps letter labels** of the symmetrized alphabet. -/
theorem label_letter {D : RelGenSet G Lambda}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (d : (diagram Delta j hlen).toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter ((diagram Delta j hlen).label d) :=
  label_admissible Delta j hlen (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) hlabel d

/-- **An arc of the exterior traversal avoiding `α w_j` goes to its image under the dart
embedding**, at the same start position. -/
theorem outerArc_mapTo_darts (arc : CyclicArc (outerDarts Delta))
    (havoid : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      arc.darts) :
    (arc.mapTo (outerImage Delta j hlen) (outerDarts_eq Delta j hlen)).darts =
      arc.darts.map (embedding Delta j hlen).darts :=
  (CyclicArc.mapTo_darts arc (outerImage Delta j hlen) (outerDarts_eq Delta j hlen)).trans
    (List.map_congr_left fun _ hd => outerImage_of_ne Delta j hlen fun h => havoid (h ▸ hd))

end OuterSpurThickening

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The target arc avoids `α w_j`** when the face of `α w_j` is not in the face set: the
target arc lies on the boundary cycle, whose darts have their faces in the face set. -/
theorem alpha_outerSpurDart_not_mem_targetArc (K : PocketFaceSet D eps X lo hi)
    (j : Fin (X.faceBoundary X.outerFace).darts.length)
    (hs2 : X.toCombMap.faceOf (X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j)) ∉
      K.faces) :
    X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts := by
  intro h
  have hmem :
      X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∈ K.boundary.cycle := by
    rw [K.decomposition]
    exact List.mem_append_right _ h
  exact hs2 ((K.boundary.cycle_mem_iff _).mp hmem).1

/-- **The pocket face set across the thickening of an outer spur**, when the target arc avoids
`α w_j`: the image faces and cells, with the boundary cycle, the source arc and the sides mapped
by the dart embedding, and the target arc mapped along the exterior traversal at the same start
position. -/
noncomputable def outerSpurThickening (K : PocketFaceSet D eps X lo hi)
    (j : Fin (X.faceBoundary X.outerFace).darts.length)
    (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
    (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts) :
    PocketFaceSet D eps (OuterSpurThickening.diagram X j hlen) lo hi where
  faces := (OuterSpurThickening.embedding X j hlen).faceSet K.faces
  outerFace_not_mem := by
    change (OuterSpurThickening.diagram X j hlen).outerFace ∉
      K.faces.map (OuterSpurThickening.embedding X j hlen).faces
    rw [(OuterSpurThickening.embedding X j hlen).outer, Finset.mem_map']
    exact K.outerFace_not_mem
  source := (OuterSpurThickening.cellMap X j hlen).indexEquiv K.source
  source_not_mem := by
    rw [(OuterSpurThickening.cellMap X j hlen).indexed_cell K.source,
      (OuterSpurThickening.cellMap X j hlen).face_eq]
    change (OuterSpurThickening.embedding X j hlen).faces (Embedded.cell X K.source).face ∉
      K.faces.map (OuterSpurThickening.embedding X j hlen).faces
    rw [Finset.mem_map']
    exact K.source_not_mem
  kept := (OuterSpurThickening.cellMap X j hlen).indexEquiv K.kept
  kept_mem := by
    rw [(OuterSpurThickening.cellMap X j hlen).indexed_cell K.kept,
      (OuterSpurThickening.cellMap X j hlen).face_eq]
    change (OuterSpurThickening.embedding X j hlen).faces (Embedded.cell X K.kept).face ∈
      K.faces.map (OuterSpurThickening.embedding X j hlen).faces
    rw [Finset.mem_map']
    exact K.kept_mem
  sourceArc := K.sourceArc.mapTo (OuterSpurThickening.embedding X j hlen).darts
    (OuterSpurThickening.cellDarts_eq X j hlen K.source)
  targetArc := K.targetArc.mapTo (OuterSpurThickening.outerImage X j hlen)
    (OuterSpurThickening.outerDarts_eq X j hlen)
  firstSide := K.firstSide.map (OuterSpurThickening.embedding X j hlen).darts
  secondSide := K.secondSide.map (OuterSpurThickening.embedding X j hlen).darts
  boundary := (OuterSpurThickening.embedding X j hlen).boundaryCycle K.faces
    K.outerFace_not_mem K.boundary
  decomposition := by
    change K.boundary.cycle.map (OuterSpurThickening.embedding X j hlen).darts = _
    rw [CyclicArc.mapTo_darts K.sourceArc (OuterSpurThickening.embedding X j hlen).darts
        (OuterSpurThickening.cellDarts_eq X j hlen K.source),
      DiscEmbeddingAway.invDarts_map, K.decomposition]
    simp only [List.map_append]
    -- The two dart types of the target arc agree only after unfolding `diagram`, so no `rw`.
    exact congrArg (HAppend.hAppend _)
      (OuterSpurThickening.outerArc_mapTo_darts X j hlen K.targetArc htgt).symm
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

variable (K : PocketFaceSet D eps X lo hi) (j : Fin (X.faceBoundary X.outerFace).darts.length)
  (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
  (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts)

theorem outerSpurThickening_faces :
    (K.outerSpurThickening j hlen htgt).faces =
      (OuterSpurThickening.embedding X j hlen).faceSet K.faces :=
  rfl

theorem outerSpurThickening_source :
    (K.outerSpurThickening j hlen htgt).source =
      (OuterSpurThickening.cellMap X j hlen).indexEquiv K.source :=
  rfl

theorem outerSpurThickening_kept :
    (K.outerSpurThickening j hlen htgt).kept =
      (OuterSpurThickening.cellMap X j hlen).indexEquiv K.kept :=
  rfl

theorem outerSpurThickening_boundary_cycle :
    (K.outerSpurThickening j hlen htgt).boundary.cycle =
      K.boundary.cycle.map (OuterSpurThickening.embedding X j hlen).darts :=
  rfl

theorem outerSpurThickening_firstSide :
    (K.outerSpurThickening j hlen htgt).firstSide =
      K.firstSide.map (OuterSpurThickening.embedding X j hlen).darts :=
  rfl

theorem outerSpurThickening_secondSide :
    (K.outerSpurThickening j hlen htgt).secondSide =
      K.secondSide.map (OuterSpurThickening.embedding X j hlen).darts :=
  rfl

theorem outerSpurThickening_sourceArc_darts :
    (K.outerSpurThickening j hlen htgt).sourceArc.darts =
      K.sourceArc.darts.map (OuterSpurThickening.embedding X j hlen).darts :=
  CyclicArc.mapTo_darts K.sourceArc (OuterSpurThickening.embedding X j hlen).darts
    (OuterSpurThickening.cellDarts_eq X j hlen K.source)

theorem outerSpurThickening_sourceArc_start :
    (K.outerSpurThickening j hlen htgt).sourceArc.start.val = K.sourceArc.start.val :=
  CyclicArc.mapTo_start K.sourceArc (OuterSpurThickening.embedding X j hlen).darts
    (OuterSpurThickening.cellDarts_eq X j hlen K.source)

theorem outerSpurThickening_sourceArc_length :
    (K.outerSpurThickening j hlen htgt).sourceArc.length = K.sourceArc.length :=
  CyclicArc.mapTo_length K.sourceArc (OuterSpurThickening.embedding X j hlen).darts
    (OuterSpurThickening.cellDarts_eq X j hlen K.source)

theorem outerSpurThickening_targetArc_darts :
    (K.outerSpurThickening j hlen htgt).targetArc.darts =
      K.targetArc.darts.map (OuterSpurThickening.embedding X j hlen).darts :=
  OuterSpurThickening.outerArc_mapTo_darts X j hlen K.targetArc htgt

/-- **The target arc keeps its start position** on the exterior traversal. -/
theorem outerSpurThickening_targetArc_start :
    (K.outerSpurThickening j hlen htgt).targetArc.start.val = K.targetArc.start.val :=
  CyclicArc.mapTo_start K.targetArc (OuterSpurThickening.outerImage X j hlen)
    (OuterSpurThickening.outerDarts_eq X j hlen)

theorem outerSpurThickening_targetArc_length :
    (K.outerSpurThickening j hlen htgt).targetArc.length = K.targetArc.length :=
  CyclicArc.mapTo_length K.targetArc (OuterSpurThickening.outerImage X j hlen)
    (OuterSpurThickening.outerDarts_eq X j hlen)

/-- **The thickening keeps walk order.** -/
theorem outerSpurThickening_closedWalk (hK : K.ClosedWalk) :
    (K.outerSpurThickening j hlen htgt).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (OuterSpurThickening.embedding X j hlen).darts).IsChain
      (fun d e => (OuterSpurThickening.diagram X j hlen).toCombMap.vertexOf
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha d) =
          (OuterSpurThickening.diagram X j hlen).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (OuterSpurThickening.vertexOf_alpha_embedding_eq_iff X j hlen d e).mpr h)
  · change (OuterSpurThickening.diagram X j hlen).toCombMap.vertexOf
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
          ((K.boundary.cycle.map (OuterSpurThickening.embedding X j hlen).darts).getLast
            (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty)) =
      (OuterSpurThickening.diagram X j hlen).toCombMap.vertexOf
        ((K.boundary.cycle.map (OuterSpurThickening.embedding X j hlen).darts).head
          (K.outerSpurThickening j hlen htgt).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (OuterSpurThickening.vertexOf_alpha_embedding_eq_iff X j hlen _ _).mpr hK.2

/-- **The thickening keeps the repeated visits.** -/
theorem outerSpurThickening_repeatedVisits :
    (K.outerSpurThickening j hlen htgt).repeatedVisits = K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  rw [outerSpurThickening_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((OuterSpurThickening.diagram X j hlen).toCombMap.vertexOf ∘
      (OuterSpurThickening.embedding X j hlen).darts)
    X.toCombMap.vertexOf
    (fun a b => OuterSpurThickening.vertexOf_embedding_eq_iff X j hlen a b) _

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.vertexOf_alpha_embedding_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.label_letter
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.outerArc_mapTo_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.alpha_outerSpurDart_not_mem_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerSpurThickening_targetArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerSpurThickening_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.outerSpurThickening_repeatedVisits
