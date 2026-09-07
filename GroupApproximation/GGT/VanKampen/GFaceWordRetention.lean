import GroupApproximation.GGT.VanKampen.GFaceSimpleWordInsertion
import GroupApproximation.GGT.VanKampen.GEdgeWordRetention
import GroupApproximation.GGT.VanKampen.GEdgeWordCellMap
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

/-!
# Actual retention of untouched regions under prescribed word insertion

The constructed embedding keeps every old dart with its label and reversal,
and every untouched face with its exact ordered traversal. It therefore
transports face-set boundaries and their shellings through the actual surgery.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC EdgeInsertion
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

section Retention

variable {D : RelGenSet G Lambda} (Delta : DiscDiagram.{u, w, v} W)
  (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
  (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
  (letter : RelLetter G Lambda)
  (hvalue : letter.val =
    RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label))
  {word : List (RelLetter G Lambda)}
  (R : GEdgeWordSubdivision.Output D
    (GFaceEdgeInsertion.diagram Delta f k hf hcells letter hvalue) (some none) word)

private theorem old_ne_positive (d : Delta.toCombMap.Dart) :
    embed Delta.toCombMap d ≠ (some none : EdgeInsertion.Dart Delta.toCombMap) := by
  intro h
  cases h

include f k in
private theorem old_ne_negative (d : Delta.toCombMap.Dart) :
    embed Delta.toCombMap d ≠ (GFaceEdgeInsertion.map Delta f k).alpha (some none) := by
  intro h
  cases h

noncomputable def initialCellMap :
    Surgery.OrderedRCellMap Delta (GFaceEdgeInsertion.diagram Delta f k hf hcells letter hvalue)
      (GFaceEdgeInsertion.keep Delta f k) where
  cell := GFaceEdgeInsertion.cell Delta f k
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- Constructed from the actual one-edge insertion and its actual subdivision. -/
noncomputable def retainedEmbedding : DiscEmbeddingAway Delta R.diagram f where
  darts := ⟨fun d => R.expansion.toDartExpansion.first (embed Delta.toCombMap d),
    R.expansion.toDartExpansion.first_injective.comp (embed_injective Delta.toCombMap)⟩
  faces := ⟨fun g => R.expansion.faceEquiv (GFaceEdgeInsertion.keep Delta f k g),
    R.expansion.faceEquiv.injective.comp (GFaceEdgeInsertion.keep_injective Delta f k)⟩
  alpha d := R.other_alpha _ (old_ne_positive Delta d) (old_ne_negative Delta f k d)
  label d := R.other_label _ (old_ne_positive Delta d) (old_ne_negative Delta f k d)
  outer := R.expansion.outerFace_eq
  face_boundary := by
    intro g hg
    refine (R.expansion.boundary_darts (GFaceEdgeInsertion.keep Delta f k g)).trans ?_
    have hboundary :
        ((GFaceEdgeInsertion.diagram Delta f k hf hcells letter hvalue).faceBoundary
          (GFaceEdgeInsertion.keep Delta f k g)).darts =
          (Delta.faceBoundary g).darts.map (embed Delta.toCombMap) :=
      allFaceBoundary_kept Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k g hg
    let expandR : EdgeInsertion.Dart Delta.toCombMap → List R.diagram.toCombMap.Dart :=
      R.expansion.darts
    refine (congrArg (fun l : List (EdgeInsertion.Dart Delta.toCombMap) =>
      l.flatMap expandR) hboundary).trans ?_
    rw [List.flatMap_map]
    trans (Delta.faceBoundary g).darts.flatMap
      (fun d => [R.expansion.toDartExpansion.first (embed Delta.toCombMap d)])
    · apply List.flatMap_congr
      intro d _
      exact R.other_darts _ (old_ne_positive Delta d) (old_ne_negative Delta f k d)
    · change (Delta.faceBoundary g).darts.flatMap
          (fun d => [R.expansion.toDartExpansion.first (embed Delta.toCombMap d)]) =
          (Delta.faceBoundary g).darts.map
            (fun d => R.expansion.toDartExpansion.first (embed Delta.toCombMap d))
      exact (List.flatMap_map _ _ _).symm.trans (List.flatMap_singleton'
        ((Delta.faceBoundary g).darts.map
          (fun d => R.expansion.toDartExpansion.first (embed Delta.toCombMap d))))
  facePerm := by
    intro d hd
    change R.diagram.toCombMap.facePerm
      (R.expansion.toDartExpansion.first (embed Delta.toCombMap d)) = _
    refine (R.other_facePerm _ (old_ne_positive Delta d) (old_ne_negative Delta f k d)).trans ?_
    exact congrArg R.expansion.toDartExpansion.first
      (facePerm_embed_of_ne Delta.toCombMap _ _ d
        (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) k)
        (by rwa [firstCorner_face]))

end Retention

structure RetainedOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) extends SimpleOutput D Delta f k word where
  embedding : DiscEmbeddingAway Delta diagram f
  vertex_darts : ∀ d, diagram.toCombMap.vertexOf (embedding.darts d) =
    vertices (Delta.toCombMap.vertexOf d)
  path_disjoint : ∀ x ∈ darts, x ∉ Set.range embedding.darts

structure CellOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) extends RetainedOutput D Delta f k word where
  cellMap : Surgery.OrderedRCellMap Delta diagram embedding.faces

theorem exists_cell_output (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    Nonempty (CellOutput D Delta f k word) := by
  let letter : RelLetter G Lambda := .base (RelLetter.listVal word)
  let Xi := GFaceEdgeInsertion.diagram Delta f k hf hcells letter hvalue
  let p : Xi.toCombMap.Dart := some none
  obtain ⟨rich⟩ := GEdgeWordSubdivision.exists_cell_output D hsymm word hne hword Xi p
    (GFaceEdgeInsertion.inserted_outer Delta f k hf)
    (GFaceEdgeInsertion.inserted_cells Delta f k hf hcells letter hvalue)
    (GFaceEdgeInsertion.label_away_inserted Delta f k hf hcells letter hvalue D hlabel) rfl
  let R := rich.toOutput
  let E := R.expansion.toDartExpansion
  let V := GFaceEdgeInsertion.vertexEquiv Delta f k
  have hfirst : Xi.toCombMap.vertexOf p =
      V.symm (Delta.toCombMap.vertexOf (firstCorner Delta.toCombMap (Delta.faceBoundary f))) :=
    (V.symm_apply_apply _).symm.trans
      (congrArg V.symm (GFaceEdgeInsertion.vertex_positive Delta f k))
  have hlast : Xi.toCombMap.vertexOf (Xi.toCombMap.alpha p) =
      V.symm (Delta.toCombMap.vertexOf (secondCorner Delta.toCombMap (Delta.faceBoundary f) k)) :=
    (V.symm_apply_apply _).symm.trans
      (congrArg V.symm (GFaceEdgeInsertion.vertex_negative Delta f k))
  have C := GFaceEdgeInsertion.orderedCells Delta f k hf hcells letter hvalue
  refine ⟨{
    diagram := R.diagram
    boundaryWord_eq := R.expansion.outerWord_eq.trans
      (GFaceEdgeInsertion.boundaryWord_eq Delta f k hf hcells letter hvalue)
    cells := ⟨R.expansion.cells.words_eq.trans C.words_eq, R.expansion.cells.values_eq.trans C.values_eq⟩
    vertices := ⟨fun v => E.vertexMap (V.symm v), E.vertexMap_injective.comp V.symm.injective⟩
    darts := E.darts p
    nonempty := E.nonempty p
    nodup := R.nodup
    chain := E.path_chain p
    word_eq := R.word_eq
    initial := (E.vertex_first p).trans (congrArg E.vertexMap hfirst)
    terminal := (E.vertex_last p).trans (congrArg E.vertexMap hlast)
    label_admissible := R.label_admissible
    faceCount_eq := (Nat.card_congr R.expansion.faceEquiv.symm).trans
      (GFaceEdgeInsertion.faceCount_eq Delta f k hf hcells letter hvalue)
    internal_fresh := ?_
    internal_vertex_eq_iff := E.internal_vertex_eq_iff p
    edge_eq_iff := E.edge_eq_iff p
    embedding := retainedEmbedding Delta f k hf hcells letter hvalue R
    cellMap := (initialCellMap Delta f k hf hcells letter hvalue).trans rich.cells
    vertex_darts := ?_
    path_disjoint := ?_ }⟩
  · intro i hi hv
    obtain ⟨v, hv⟩ := hv
    exact E.internal_fresh p i hi ⟨V.symm v, hv⟩
  · intro d
    change R.diagram.toCombMap.vertexOf (E.first (embed Delta.toCombMap d)) =
      E.vertexMap (V.symm (Delta.toCombMap.vertexOf d))
    rw [E.vertex_first]
    exact congrArg E.vertexMap ((V.symm_apply_apply _).symm)
  · intro x hx h
    obtain ⟨d, hd⟩ := h
    change E.first (embed Delta.toCombMap d) = x at hd
    have hmem : x ∈ E.darts (embed Delta.toCombMap d) :=
      hd ▸ List.head_mem (E.nonempty (embed Delta.toCombMap d))
    have heq := E.block_eq_of_mem hx hmem
    change (some none : EdgeInsertion.Dart Delta.toCombMap) = some (some d) at heq
    cases heq

/-- The original retained-output interface follows from the stronger actual producer. -/
theorem exists_retained_output (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    Nonempty (RetainedOutput D Delta f k word) := by
  obtain ⟨R⟩ := exists_cell_output D hsymm Delta hlabel f k hf hcells word hne hword hvalue
  exact ⟨R.toRetainedOutput⟩

namespace RetainedOutput

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
  {f : Delta.toCombMap.Face} {k : Fin (Delta.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)} (R : RetainedOutput D Delta f k word)

/-- The new path shares no old edge, in either orientation. -/
theorem path_edge_ne (x : R.diagram.toCombMap.Dart) (hx : x ∈ R.darts)
    (d : Delta.toCombMap.Dart) :
    R.diagram.toCombMap.edgeOf x ≠ R.diagram.toCombMap.edgeOf (R.embedding.darts d) := by
  intro h
  rcases (R.diagram.toCombMap.edgeOf_eq_iff _ _).mp h with h | h
  · exact R.path_disjoint x hx ⟨d, h.symm⟩
  · have heq : x = R.embedding.darts (Delta.toCombMap.alpha d) := by
      rw [← R.embedding.alpha]
      exact (R.diagram.toCombMap.alpha_involutive x).symm.trans
        (congrArg R.diagram.toCombMap.alpha h)
    exact R.path_disjoint x hx ⟨Delta.toCombMap.alpha d, heq.symm⟩

/-- A selected region avoiding the insertion face retains its actual boundary and pasting. -/
theorem region_pasting (s : Finset Delta.toCombMap.Face) (hf : f ∉ s)
    (B : Embedded.FaceSetBoundary Delta s)
    (H : ∃ l, Embedded.FaceShelling Delta s l B.cycle) :
    ∃ l, Embedded.FaceShelling R.diagram (R.embedding.faceSet s) l
      (R.embedding.boundary s hf B).cycle := by
  obtain ⟨l, hl⟩ := H
  exact ⟨l.map R.embedding.faces, R.embedding.shelling s hf hl⟩

end RetainedOutput

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.retainedEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.initialCellMap
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_cell_output
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_retained_output
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.RetainedOutput.path_edge_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.RetainedOutput.region_pasting
