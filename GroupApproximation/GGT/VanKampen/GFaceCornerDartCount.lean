import GroupApproximation.GGT.VanKampen.GFaceCornerInsertion
import GroupApproximation.Meta.AxiomGuard

/-!
# Dart count of a corner insertion

Inserting a word of length `n` across a `G`-face, from corner to corner, adds `2 n` darts.  The
insertion is an edge insertion, which adds the two darts of one new edge
(`GFaceEdgeInsertion.dartCount_eq`), followed by the subdivision of the new edge into `n`
edges.  Every dart of the subdivided diagram lies in the block of an old dart
(`DiscExpansion.exists_old_dart`), the blocks are disjoint, the two darts of the subdivided edge
have blocks of length `n` and every other block is a single dart
(`GEdgeWordSubdivision.Output.dartCount_add_two`).

`GFaceWordInsertion.exists_cell_output_dartCount` is `exists_cell_output_of_reversible` with the
count, and `GFaceWordInsertion.exists_corner_output_dartCount` is `exists_corner_output` with
the count.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace GEdgeWordSubdivision

/-- **Subdividing an edge by a word of length `n` replaces its two darts by `2 n` darts.** -/
theorem Output.dartCount_add_two {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    {a : Delta.toCombMap.Dart} {word : List (RelLetter G Lambda)} (R : Output D Delta a word) :
    R.diagram.toCombMap.dartCount + 2 = Delta.toCombMap.dartCount + 2 * word.length := by
  classical
  have hnodup : ((Finset.univ : Finset Delta.toCombMap.Dart).toList.flatMap
      R.expansion.darts).Nodup :=
    R.expansion.nodup _ (Finset.nodup_toList _)
  have hcover : ((Finset.univ : Finset Delta.toCombMap.Dart).toList.flatMap
      R.expansion.darts).toFinset = Finset.univ := by
    refine Finset.eq_univ_of_forall fun x => ?_
    obtain ⟨d, hd⟩ := R.expansion.exists_old_dart x
    exact List.mem_toFinset.mpr
      (List.mem_flatMap.mpr ⟨d, Finset.mem_toList.mpr (Finset.mem_univ d), hd⟩)
  have hcount : R.diagram.toCombMap.dartCount =
      ∑ d : Delta.toCombMap.Dart, (R.expansion.darts d).length := by
    rw [CombMap.dartCount, Nat.card_eq_fintype_card, ← Finset.card_univ, ← hcover,
      List.toFinset_card_of_nodup hnodup, List.length_flatMap, Finset.sum_map_toList]
  have hmem : Delta.toCombMap.alpha a ∈ (Finset.univ : Finset Delta.toCombMap.Dart).erase a :=
    Finset.mem_erase.mpr ⟨Delta.toCombMap.alpha_fixedPointFree a, Finset.mem_univ _⟩
  have hsplit : (R.expansion.darts a).length +
      ((R.expansion.darts (Delta.toCombMap.alpha a)).length +
        ∑ d ∈ ((Finset.univ : Finset Delta.toCombMap.Dart).erase a).erase
          (Delta.toCombMap.alpha a), (R.expansion.darts d).length) =
      ∑ d : Delta.toCombMap.Dart, (R.expansion.darts d).length := by
    rw [Finset.add_sum_erase _ (fun d => (R.expansion.darts d).length) hmem,
      Finset.add_sum_erase _ (fun d => (R.expansion.darts d).length) (Finset.mem_univ a)]
  have hrest : ∑ d ∈ ((Finset.univ : Finset Delta.toCombMap.Dart).erase a).erase
      (Delta.toCombMap.alpha a), (R.expansion.darts d).length =
      (((Finset.univ : Finset Delta.toCombMap.Dart).erase a).erase
        (Delta.toCombMap.alpha a)).card * 1 := by
    refine Finset.sum_const_nat fun d hd => ?_
    obtain ⟨hdb, hd⟩ := Finset.mem_erase.mp hd
    obtain ⟨hda, -⟩ := Finset.mem_erase.mp hd
    simpa only [List.length_map, List.length_singleton] using
      congrArg List.length (R.other_word d hda hdb)
  have hcard : (((Finset.univ : Finset Delta.toCombMap.Dart).erase a).erase
      (Delta.toCombMap.alpha a)).card + 1 + 1 = Delta.toCombMap.dartCount := by
    rw [Finset.card_erase_add_one hmem, Finset.card_erase_add_one (Finset.mem_univ a),
      Finset.card_univ, CombMap.dartCount, Nat.card_eq_fintype_card]
  have hreverse : (R.expansion.darts (Delta.toCombMap.alpha a)).length = word.length := by
    rw [R.expansion.reverse, List.length_map, List.length_reverse, R.length_eq]
  have hlength := R.length_eq
  omega

end GEdgeWordSubdivision

namespace GFaceEdgeInsertion

/-- **Inserting an edge across a face adds two darts.** -/
theorem dartCount_eq (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
    (k : Fin (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f) (letter : RelLetter G Lambda)
    (hprefix : letter.val =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    (diagram Delta f k hf hcells letter hprefix).toCombMap.dartCount =
      Delta.toCombMap.dartCount + 2 := by
  have h1 : Fintype.card (Option (Option Delta.toCombMap.Dart)) =
      Fintype.card (Option Delta.toCombMap.Dart) + 1 :=
    Fintype.card_option
  have h2 : Fintype.card (Option Delta.toCombMap.Dart) = Fintype.card Delta.toCombMap.Dart + 1 :=
    Fintype.card_option
  change Nat.card (Option (Option Delta.toCombMap.Dart)) = Nat.card Delta.toCombMap.Dart + 2
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

end GFaceEdgeInsertion

namespace GFaceWordInsertion

open HullSC EdgeInsertion

/-- `exists_cell_output_of_reversible`, with the dart count of the output: the insertion adds
`2 |word|` darts. -/
theorem exists_cell_output_dartCount (D : RelGenSet G Lambda)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hinv : ∀ letter ∈ word, D.IsLetter (RelWord.inv letter))
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    ∃ R : CellOutput D Delta f k word,
      R.diagram.toCombMap.dartCount = Delta.toCombMap.dartCount + 2 * word.length := by
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
  have hfirst : Xi.toCombMap.vertexOf p =
      V.symm (Delta.toCombMap.vertexOf (firstCorner Delta.toCombMap (Delta.faceBoundary f))) :=
    (V.symm_apply_apply _).symm.trans
      (congrArg V.symm (GFaceEdgeInsertion.vertex_positive Delta f k))
  have hlast : Xi.toCombMap.vertexOf (Xi.toCombMap.alpha p) =
      V.symm (Delta.toCombMap.vertexOf (secondCorner Delta.toCombMap (Delta.faceBoundary f) k)) :=
    (V.symm_apply_apply _).symm.trans
      (congrArg V.symm (GFaceEdgeInsertion.vertex_negative Delta f k))
  have C := GFaceEdgeInsertion.orderedCells Delta f k hf hcells letter hvalue
  have hcount : R.diagram.toCombMap.dartCount = Delta.toCombMap.dartCount + 2 * word.length := by
    have hsub := R.dartCount_add_two
    have hedge : Xi.toCombMap.dartCount = Delta.toCombMap.dartCount + 2 :=
      GFaceEdgeInsertion.dartCount_eq Delta f k hf hcells letter hvalue
    omega
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
    path_disjoint := ?_ }, hcount⟩
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

/-- **A corner insertion with its dart count.**  `exists_corner_output`, with the dart count of
the output: inserting `word` from corner to corner adds `2 |word|` darts. -/
theorem exists_corner_output_dartCount (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (start finish : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : RelWord.IsAdmissible D word)
    (hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l))
    (hvalue : RelLetter.listVal word = RelLetter.listVal
      ((((Delta.faceBoundary f).darts.rotate start.val).take
        ((Delta.faceBoundary f).forwardOffset start finish)).map Delta.label)) :
    ∃ R : CornerOutput D Delta f hf hcells start finish word,
      R.diagram.toCombMap.dartCount = Delta.toCombMap.dartCount + 2 * word.length :=
  exists_cell_output_dartCount D (GFaceRebase.diagram Delta f start.val hf hcells) hlabel f
    (GFaceRebase.cornerIndex Delta f hf hcells start finish) hf hcells word hne hword hinv
    (by simpa only [GFaceRebase.diagram, GFaceRebase.boundary, ite_true, GFaceRebase.cornerIndex,
      FaceBoundary.rotate] using hvalue)

end GFaceWordInsertion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.Output.dartCount_add_two
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.dartCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_cell_output_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_corner_output_dartCount
