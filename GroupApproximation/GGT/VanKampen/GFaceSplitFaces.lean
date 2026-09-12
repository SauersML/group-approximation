import GroupApproximation.GGT.VanKampen.GFaceWordRetention
import GroupApproximation.GGT.VanKampen.CombMapEdgeBoundaries
import GroupApproximation.Meta.AxiomGuard

/-!
# The two faces a word insertion splits a G-face into

`GFaceWordInsertion.CellOutput` inserts a prescribed word path across a G-face `f`
between its first corner and the corner at index `k`, and records how every OTHER face
survives (`DiscEmbeddingAway`).  The surgeries of Osin's Appendix (arXiv:math/0411039v3,
§9: the new contiguity subdiagram of Lemma 9.4 Case 1, the merges of Lemma 9.7(a)) need
the two NEW faces as well: the region is one of them.  This file records them.

At the one-edge level (`EdgeInsertion.allFaceBoundary_prefix/_suffix`) the inserted edge
closes the prefix `f_0 … f_{k-1}` of the old traversal with its negative dart and the
suffix `f_k …` with its positive dart.  The word subdivision expands the positive dart
into the inserted path, its reverse into the reversed path, and every old dart into
itself.  So after the insertion:

* the prefix side reads the reversed path, then the retained prefix of `f`;
* the suffix side reads the path, then the retained suffix of `f`;

(`SplitOutput.prefixSide_darts`, `SplitOutput.suffixSide_darts`), and the two sides are
different faces.  `exists_split_output_of_reversible` is the producer; it is the landed
producer `exists_cell_output_of_reversible` with the two sides added.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC EdgeInsertion
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **A word insertion across `f`, with the two faces it splits `f` into.** -/
structure SplitOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) extends CellOutput D Delta f k word where
  /-- The face closing the prefix of the old traversal. -/
  prefixSide : diagram.toCombMap.Face
  /-- The face closing the suffix of the old traversal. -/
  suffixSide : diagram.toCombMap.Face
  prefixSide_ne_suffixSide : prefixSide ≠ suffixSide
  /-- The prefix side reads the reversed path, then the retained prefix. -/
  prefixSide_darts : (diagram.faceBoundary prefixSide).darts =
    Embedded.invDarts diagram darts ++
      ((Delta.faceBoundary f).darts.take k.val).map embedding.darts
  /-- The suffix side reads the path, then the retained suffix. -/
  suffixSide_darts : (diagram.faceBoundary suffixSide).darts =
    darts ++ ((Delta.faceBoundary f).darts.drop k.val).map embedding.darts
  /-- A retained old face other than `f` is not the prefix side. -/
  prefixSide_not_kept : ∀ g, g ≠ f → embedding.faces g ≠ prefixSide
  /-- A retained old face other than `f` is not the suffix side. -/
  suffixSide_not_kept : ∀ g, g ≠ f → embedding.faces g ≠ suffixSide

/-- **The producer**: the landed word insertion, with its two sides. -/
theorem exists_split_output_of_reversible (D : RelGenSet G Lambda)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hinv : ∀ letter ∈ word, D.IsLetter (RelWord.inv letter))
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    Nonempty (SplitOutput D Delta f k word) := by
  let letter : RelLetter G Lambda := .base (RelLetter.listVal word)
  let Xi := GFaceEdgeInsertion.diagram Delta f k hf hcells letter hvalue
  let p : Xi.toCombMap.Dart := some none
  obtain ⟨rich⟩ := GEdgeWordSubdivision.exists_cell_output_of_reversible D word hne hword hinv Xi p
    (GFaceEdgeInsertion.inserted_outer Delta f k hf)
    (GFaceEdgeInsertion.inserted_cells Delta f k hf hcells letter hvalue)
    (GFaceEdgeInsertion.label_away_inserted Delta f k hf hcells letter hvalue D hlabel) rfl
  let R := rich.toOutput
  let E := R.expansion.toDartExpansion
  let V := GFaceEdgeInsertion.vertexEquiv Delta f k
  let expandR : EdgeInsertion.Dart Delta.toCombMap → List R.diagram.toCombMap.Dart :=
    R.expansion.darts
  have hfirst : Xi.toCombMap.vertexOf p =
      V.symm (Delta.toCombMap.vertexOf (firstCorner Delta.toCombMap (Delta.faceBoundary f))) :=
    (V.symm_apply_apply _).symm.trans
      (congrArg V.symm (GFaceEdgeInsertion.vertex_positive Delta f k))
  have hlast : Xi.toCombMap.vertexOf (Xi.toCombMap.alpha p) =
      V.symm (Delta.toCombMap.vertexOf (secondCorner Delta.toCombMap (Delta.faceBoundary f) k)) :=
    (V.symm_apply_apply _).symm.trans
      (congrArg V.symm (GFaceEdgeInsertion.vertex_negative Delta f k))
  have C := GFaceEdgeInsertion.orderedCells Delta f k hf hcells letter hvalue
  have hnone : expandR none = Embedded.invDarts R.diagram (R.expansion.darts p) :=
    R.expansion.reverse p
  have hsome : expandR (some none) = R.expansion.darts p := rfl
  have hold : ∀ l : List Delta.toCombMap.Dart,
      (l.map (EdgeInsertion.embed Delta.toCombMap)).flatMap expandR =
        l.map (fun d => E.first (EdgeInsertion.embed Delta.toCombMap d)) := by
    intro l
    rw [List.flatMap_map]
    trans l.flatMap (fun d => [E.first (EdgeInsertion.embed Delta.toCombMap d)])
    · apply List.flatMap_congr
      intro d _
      refine R.other_darts _ (fun h => ?_) (fun h => ?_)
      · change EdgeInsertion.embed Delta.toCombMap d =
          (some none : EdgeInsertion.Dart Delta.toCombMap) at h
        cases h
      · change EdgeInsertion.embed Delta.toCombMap d =
          (GFaceEdgeInsertion.map Delta f k).alpha (some none) at h
        cases h
    · exact (List.flatMap_map _ _ _).symm.trans
        (List.flatMap_singleton' (l.map (fun d => E.first (EdgeInsertion.embed Delta.toCombMap d))))
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
    path_disjoint := ?_
    prefixSide := R.expansion.faceEquiv
      (EdgeInsertion.prefixFace Delta.toCombMap (Delta.faceBoundary f) k)
    suffixSide := R.expansion.faceEquiv
      (EdgeInsertion.suffixFace Delta.toCombMap (Delta.faceBoundary f) k)
    prefixSide_ne_suffixSide := fun h =>
      EdgeInsertion.prefixFace_ne_suffixFace Delta.toCombMap (Delta.faceBoundary f) k
        (R.expansion.faceEquiv.injective h)
    prefixSide_darts := (R.expansion.boundary_darts _).trans
      ((congrArg (fun l : List (EdgeInsertion.Dart Delta.toCombMap) => l.flatMap expandR)
        (EdgeInsertion.allFaceBoundary_prefix Delta.toCombMap (Delta.faceBoundary f)
          Delta.faceBoundary k)).trans
        (List.flatMap_cons.trans (congrArg₂ (· ++ ·) hnone (hold _))))
    suffixSide_darts := (R.expansion.boundary_darts _).trans
      ((congrArg (fun l : List (EdgeInsertion.Dart Delta.toCombMap) => l.flatMap expandR)
        (EdgeInsertion.allFaceBoundary_suffix Delta.toCombMap (Delta.faceBoundary f)
          Delta.faceBoundary k)).trans
        (List.flatMap_cons.trans (congrArg₂ (· ++ ·) hsome (hold _))))
    prefixSide_not_kept := fun g hg h =>
      EdgeInsertion.keptFace_ne_prefixFace Delta.toCombMap (Delta.faceBoundary f) k g hg
        (R.expansion.faceEquiv.injective h)
    suffixSide_not_kept := fun g hg h =>
      EdgeInsertion.keptFace_ne_suffixFace Delta.toCombMap (Delta.faceBoundary f) k g hg
        (R.expansion.faceEquiv.injective h) }⟩
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

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_split_output_of_reversible
