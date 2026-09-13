import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarWalk
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStep
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket face set across the doubling of an edge

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pinched pocket face set passes twice through a vertex, and a vertex
splitting there (`PinchSplit.Input.diagram`) merges two G-faces in corners outside the face set,
on distinct faces away from the relator cells.  When a corner lies in a relator face, or both
corners lie in one face, the doubling of an edge (`FaceEdgeDoubling.diagram`) first fills the
corner with a G-cell digon.  When the face set avoids the doubled face and the source arc avoids
the doubled dart, the doubling keeps every old dart, label and vertex, so the pocket face set
transports by the dart embedding, with the same walk order and the same repeated visits.

* `card_toFinset_map_eq_of_iff`: two maps identifying the same entries of a list take as many
  distinct values on it.
* `DiscEmbeddingAway.boundaryCycle`: the boundary cycle of a face set avoiding the insertion face,
  mapped by the dart embedding.
* `FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff`, `faceImage_mem_faceSet_iff` and
  `label_letter`: vertices, cell faces and letter labels across the doubling.
* `PocketFaceSet.faceEdgeDoubling`: the transported pocket face set.
* `PocketFaceSet.faceEdgeDoubling_closedWalk` and `faceEdgeDoubling_repeatedVisits`: walk order
  and repeated visits are unchanged.

## Manuscript status

Infrastructure for `thm:hull` (tex 1903,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v v'

open Embedded

/-- **Values identified alike are counted alike.**  If `f` and `g` identify the same entries, a
list takes as many distinct values under `f` as under `g`. -/
theorem card_toFinset_map_eq_of_iff {α β γ : Type*} {_ : DecidableEq β} {_ : DecidableEq γ}
    (f : α → β) (g : α → γ) (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    ∀ l : List α, (l.map f).toFinset.card = (l.map g).toFinset.card
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.map_cons, List.toFinset_cons, List.toFinset_cons]
    by_cases ha : f a ∈ (l.map f).toFinset
    · have hb : g a ∈ (l.map g).toFinset := by
        obtain ⟨c, hc, hca⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hc, (hfg c a).mp hca⟩)
      rw [Finset.insert_eq_of_mem ha, Finset.insert_eq_of_mem hb]
      exact card_toFinset_map_eq_of_iff f g hfg l
    · have hb : g a ∉ (l.map g).toFinset := fun hb => by
        obtain ⟨c, hc, hca⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
        exact ha (List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hc, (hfg c a).mpr hca⟩))
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb]
      exact congrArg (· + 1) (card_toFinset_map_eq_of_iff f g hfg l)

namespace DiscEmbeddingAway

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W} {f : Delta.toCombMap.Face}
  (E : DiscEmbeddingAway Delta Xi f)

/-- **The boundary cycle of a face set avoiding the insertion face, after the embedding.** -/
def boundaryCycle (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s) :
    Surgery.MapCollapse.BoundaryCycle Xi.toCombMap (E.faceSet s) where
  cycle := B.cycle.map E.darts
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := B.cycle_nodup.map E.darts.injective
  cycle_mem_iff := by
    intro d
    rw [List.mem_map]
    refine Iff.trans ?_ (E.boundary_dart_iff s hf d).symm
    constructor
    · rintro ⟨e, he, hed⟩
      exact ⟨e, hed, (B.cycle_mem_iff e).mp he⟩
    · rintro ⟨e, hed, he⟩
      exact ⟨e, (B.cycle_mem_iff e).mpr he, hed⟩

theorem boundaryCycle_cycle (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (B : Surgery.MapCollapse.BoundaryCycle Delta.toCombMap s) :
    (E.boundaryCycle s hf B).cycle = B.cycle.map E.darts :=
  rfl

end DiscEmbeddingAway

namespace FaceEdgeDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **The doubling keeps the vertices of old darts.** -/
theorem vertexOf_embedding_eq_iff (x y : Delta.toCombMap.Dart) :
    (diagram Delta f j hlen hf).toCombMap.vertexOf ((embedding Delta f j hlen hf).darts x) =
        (diagram Delta f j hlen hf).toCombMap.vertexOf ((embedding Delta f j hlen hf).darts y) ↔
      Delta.toCombMap.vertexOf x = Delta.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff Delta.toCombMap
    (EdgeInsertion.firstCorner Delta.toCombMap (rebased Delta f j))
    (EdgeInsertion.secondCorner Delta.toCombMap (rebased Delta f j) (second Delta f j hlen)) x y

/-- **The doubling keeps the vertices of old darts and their reverses.** -/
theorem vertexOf_alpha_embedding_eq_iff (x y : Delta.toCombMap.Dart) :
    (diagram Delta f j hlen hf).toCombMap.vertexOf
        ((diagram Delta f j hlen hf).toCombMap.alpha ((embedding Delta f j hlen hf).darts x)) =
        (diagram Delta f j hlen hf).toCombMap.vertexOf ((embedding Delta f j hlen hf).darts y) ↔
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha x) = Delta.toCombMap.vertexOf y := by
  rw [(embedding Delta f j hlen hf).alpha]
  exact vertexOf_embedding_eq_iff Delta f j hlen hf _ y

/-- **A transported face set holds the image of an old face exactly when the old set holds it**,
for a face set avoiding the doubled face. -/
theorem faceImage_mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (g : Delta.toCombMap.Face) :
    faceImage Delta f j hlen g ∈ (embedding Delta f j hlen hf).faceSet s ↔ g ∈ s := by
  by_cases hg : g = f
  · rw [hg, faceImage_self]
    refine ⟨fun h => ?_, fun h => (hs h).elim⟩
    obtain ⟨g', hg', hkeep⟩ := Finset.mem_map.mp h
    exact (keep_ne_cellFace Delta f j hlen (fun heq => hs (heq ▸ hg')) hkeep).elim
  · rw [faceImage_of_ne Delta f j hlen hg]
    exact Finset.mem_map' (embedding Delta f j hlen hf).faces

/-- **The doubling keeps letter labels** of the symmetrized alphabet. -/
theorem label_letter {D : RelGenSet G Lambda}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (d : (diagram Delta f j hlen hf).toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter ((diagram Delta f j hlen hf).label d) :=
  label_admissible Delta f j hlen hf (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) hlabel d

end FaceEdgeDoubling

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The pocket face set across the doubling of an edge** of a face `f` outside the face set,
when the source arc avoids the doubled dart: the image faces and cells, with the boundary cycle,
the arcs and the sides mapped by the dart embedding. -/
noncomputable def faceEdgeDoubling (K : PocketFaceSet D eps X lo hi) (f : X.toCombMap.Face)
    (j : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
    (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
    (hsrc : FaceEdgeDoubling.dart X f j ∉ K.sourceArc.darts) :
    PocketFaceSet D eps (FaceEdgeDoubling.diagram X f j hlen hf) lo hi where
  faces := (FaceEdgeDoubling.embedding X f j hlen hf).faceSet K.faces
  outerFace_not_mem := by
    rw [(FaceEdgeDoubling.embedding X f j hlen hf).outer]
    exact fun h => K.outerFace_not_mem ((Finset.mem_map' _).mp h)
  source := (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv K.source
  source_not_mem := by
    rw [(FaceEdgeDoubling.cellMap X f j hlen hf).indexed_cell K.source,
      (FaceEdgeDoubling.cellMap X f j hlen hf).face_eq]
    exact fun h => K.source_not_mem
      ((FaceEdgeDoubling.faceImage_mem_faceSet_iff X f j hlen hf hs _).mp h)
  kept := (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv K.kept
  kept_mem := by
    rw [(FaceEdgeDoubling.cellMap X f j hlen hf).indexed_cell K.kept,
      (FaceEdgeDoubling.cellMap X f j hlen hf).face_eq]
    exact (FaceEdgeDoubling.faceImage_mem_faceSet_iff X f j hlen hf hs _).mpr K.kept_mem
  sourceArc := K.sourceArc.mapTo
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X K.source).face)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf K.source)
  targetArc := K.targetArc.mapTo (FaceEdgeDoubling.embedding X f j hlen hf).darts
    ((FaceEdgeDoubling.embedding X f j hlen hf).outerDarts_eq hf)
  firstSide := K.firstSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts
  secondSide := K.secondSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts
  boundary := (FaceEdgeDoubling.embedding X f j hlen hf).boundaryCycle K.faces hs K.boundary
  decomposition := by
    have hsa : (K.sourceArc.mapTo
        (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X K.source).face)
        (FaceEdgeDoubling.cellDarts_eq X f j hlen hf K.source)).darts =
          K.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
      FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf K.sourceArc _
        (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f j hlen hf
          (Embedded.cell X K.source).face hd) _ hsrc
    rw [hsa, CyclicArc.mapTo_darts, DiscEmbeddingAway.invDarts_map,
      DiscEmbeddingAway.boundaryCycle_cycle, K.decomposition]
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
  (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
  (hsrc : FaceEdgeDoubling.dart X f j ∉ K.sourceArc.darts)

theorem faceEdgeDoubling_faces :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).faces =
      (FaceEdgeDoubling.embedding X f j hlen hf).faceSet K.faces :=
  rfl

theorem faceEdgeDoubling_source :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).source =
      (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv K.source :=
  rfl

theorem faceEdgeDoubling_boundary_cycle :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle =
      K.boundary.cycle.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  rfl

theorem faceEdgeDoubling_firstSide :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).firstSide =
      K.firstSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  rfl

theorem faceEdgeDoubling_secondSide :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).secondSide =
      K.secondSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  rfl

theorem faceEdgeDoubling_sourceArc_darts :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).sourceArc.darts =
      K.sourceArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf K.sourceArc
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X K.source).face)
    (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f j hlen hf
      (Embedded.cell X K.source).face hd)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf K.source) hsrc

theorem faceEdgeDoubling_targetArc_darts :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).targetArc.darts =
      K.targetArc.darts.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  CyclicArc.mapTo_darts K.targetArc (FaceEdgeDoubling.embedding X f j hlen hf).darts
    ((FaceEdgeDoubling.embedding X f j hlen hf).outerDarts_eq hf)

/-- **The doubling keeps walk order.** -/
theorem faceEdgeDoubling_closedWalk (hK : K.ClosedWalk) :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).ClosedWalk := by
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
            (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle_nonempty)) =
      (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf
        ((K.boundary.cycle.map (FaceEdgeDoubling.embedding X f j hlen hf).darts).head
          (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff X f j hlen hf _ _).mpr hK.2

/-- **The doubling keeps the repeated visits.** -/
theorem faceEdgeDoubling_repeatedVisits :
    (K.faceEdgeDoubling f j hlen hf hs hsrc).repeatedVisits = K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  rw [faceEdgeDoubling_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.vertexOf ∘
      (FaceEdgeDoubling.embedding X f j hlen hf).darts)
    X.toCombMap.vertexOf
    (fun a b => FaceEdgeDoubling.vertexOf_embedding_eq_iff X f j hlen hf a b) _

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.card_toFinset_map_eq_of_iff
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.boundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.vertexOf_alpha_embedding_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.faceImage_mem_faceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.label_letter
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoubling_sourceArc_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoubling_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceEdgeDoubling_repeatedVisits
