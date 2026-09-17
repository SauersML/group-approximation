import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: a cell pocket across an embedding away from its corner face

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  A dart and face embedding
`E : DiscEmbeddingAway X X' f` keeps every face boundary other than `f`.  When `f` is not in the
face set of a cell pocket `K` and neither cell of `K` has face `f`, the face set, both cells, the
kept cell, the arcs, the sides and the boundary cycle all transport by the embedding
(`transport`).  When the embedding keeps the vertices of old darts, walk order and the repeated
visits are unchanged, and both arcs stay proper.  This is the pattern of
`CellPocketFaceSet.outerSpurThickening`, for any embedding and corner face `f`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X X' : DiscDiagram.{u, w, v} W} {f : X.toCombMap.Face}
  (E : DiscEmbeddingAway X X' f) (ix : Fin X.rCellCount → Fin X'.rCellCount)
  (hcell : ∀ k, (Embedded.cell X k).face ≠ f →
    (Embedded.cell X' (ix k)).face = E.faces (Embedded.cell X k).face)

include hcell in
theorem cellDarts_transport {k : Fin X.rCellCount} (hk : (Embedded.cell X k).face ≠ f) :
    cellDarts X' (ix k) = (cellDarts X k).map E.darts := by
  change (X'.faceBoundary (Embedded.cell X' (ix k)).face).darts =
    (X.faceBoundary (Embedded.cell X k).face).darts.map E.darts
  rw [hcell k hk]
  exact E.face_boundary _ hk

variable {i j : Fin X.rCellCount}

/-- **The cell pocket across the embedding.** -/
noncomputable def transport (K : CellPocketFaceSet D eps X i j) (hs : f ∉ K.faces)
    (hi : (Embedded.cell X i).face ≠ f) (hj : (Embedded.cell X j).face ≠ f) :
    CellPocketFaceSet D eps X' (ix i) (ix j) where
  faces := E.faceSet K.faces
  outerFace_not_mem := by
    change X'.outerFace ∉ K.faces.map E.faces
    rw [E.outer, Finset.mem_map']
    exact K.outerFace_not_mem
  first_not_mem := by
    rw [hcell i hi]
    change E.faces (Embedded.cell X i).face ∉ K.faces.map E.faces
    rw [Finset.mem_map']
    exact K.first_not_mem
  second_not_mem := by
    rw [hcell j hj]
    change E.faces (Embedded.cell X j).face ∉ K.faces.map E.faces
    rw [Finset.mem_map']
    exact K.second_not_mem
  kept := ix K.kept
  kept_mem := by
    have hk : (Embedded.cell X K.kept).face ≠ f := fun h => hs (by rw [← h]; exact K.kept_mem)
    rw [hcell K.kept hk]
    change E.faces (Embedded.cell X K.kept).face ∈ K.faces.map E.faces
    rw [Finset.mem_map']
    exact K.kept_mem
  firstArc := K.firstArc.mapTo E.darts (cellDarts_transport E ix hcell hi)
  secondArc := K.secondArc.mapTo E.darts (cellDarts_transport E ix hcell hj)
  firstSide := K.firstSide.map E.darts
  secondSide := K.secondSide.map E.darts
  boundary := E.boundaryCycle K.faces hs K.boundary
  decomposition := by
    change K.boundary.cycle.map E.darts = _
    rw [CyclicArc.mapTo_darts K.firstArc E.darts (cellDarts_transport E ix hcell hi),
      CyclicArc.mapTo_darts K.secondArc E.darts (cellDarts_transport E ix hcell hj),
      DiscEmbeddingAway.invDarts_map, DiscEmbeddingAway.invDarts_map, K.decomposition]
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

theorem vertexOf_alpha_darts_iff
    (hvert : ∀ x y, X'.toCombMap.vertexOf (E.darts x) = X'.toCombMap.vertexOf (E.darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) (x y : X.toCombMap.Dart) :
    X'.toCombMap.vertexOf (X'.toCombMap.alpha (E.darts x)) =
        X'.toCombMap.vertexOf (E.darts y) ↔
      X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y := by
  rw [E.alpha]
  exact hvert _ y

variable (K : CellPocketFaceSet D eps X i j) (hs : f ∉ K.faces)
  (hi : (Embedded.cell X i).face ≠ f) (hj : (Embedded.cell X j).face ≠ f)

theorem transport_boundary_cycle :
    (transport E ix hcell K hs hi hj).boundary.cycle = K.boundary.cycle.map E.darts :=
  rfl

/-- **The embedding keeps walk order.** -/
theorem transport_closedWalk
    (hvert : ∀ x y, X'.toCombMap.vertexOf (E.darts x) = X'.toCombMap.vertexOf (E.darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) (hK : K.ClosedWalk) :
    (transport E ix hcell K hs hi hj).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map E.darts).IsChain
      (fun d e => X'.toCombMap.vertexOf (X'.toCombMap.alpha d) = X'.toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h =>
      (vertexOf_alpha_darts_iff E hvert d e).mpr h)
  · change X'.toCombMap.vertexOf (X'.toCombMap.alpha ((K.boundary.cycle.map E.darts).getLast
        (transport E ix hcell K hs hi hj).boundary.cycle_nonempty)) =
      X'.toCombMap.vertexOf ((K.boundary.cycle.map E.darts).head
        (transport E ix hcell K hs hi hj).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (vertexOf_alpha_darts_iff E hvert _ _).mpr hK.2

/-- **The embedding keeps the repeated visits.** -/
theorem transport_repeatedVisits
    (hvert : ∀ x y, X'.toCombMap.vertexOf (E.darts x) = X'.toCombMap.vertexOf (E.darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) :
    (transport E ix hcell K hs hi hj).repeatedVisits = K.repeatedVisits := by
  unfold CellPocketFaceSet.repeatedVisits
  rw [transport_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff (X'.toCombMap.vertexOf ∘ E.darts) X.toCombMap.vertexOf
    (fun a b => hvert a b) _

theorem transport_first_proper (hfirst : K.firstArc.length < (cellDarts X i).length) :
    (transport E ix hcell K hs hi hj).firstArc.length < (cellDarts X' (ix i)).length := by
  have h1 : (transport E ix hcell K hs hi hj).firstArc.length = K.firstArc.length :=
    CyclicArc.mapTo_length K.firstArc _ (cellDarts_transport E ix hcell hi)
  have h2 : (cellDarts X' (ix i)).length = (cellDarts X i).length :=
    (congrArg List.length (cellDarts_transport E ix hcell hi)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hfirst h2.symm)

theorem transport_second_proper (hsecond : K.secondArc.length < (cellDarts X j).length) :
    (transport E ix hcell K hs hi hj).secondArc.length < (cellDarts X' (ix j)).length := by
  have h1 : (transport E ix hcell K hs hi hj).secondArc.length = K.secondArc.length :=
    CyclicArc.mapTo_length K.secondArc _ (cellDarts_transport E ix hcell hj)
  have h2 : (cellDarts X' (ix j)).length = (cellDarts X j).length :=
    (congrArg List.length (cellDarts_transport E ix hcell hj)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hsecond h2.symm)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.transport
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.transport_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.transport_repeatedVisits
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.transport_first_proper
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.transport_second_proper
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.cellDarts_transport
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.vertexOf_alpha_darts_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.transport_boundary_cycle
