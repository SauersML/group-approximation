import GroupApproximation.GGT.VanKampen.GFaceWordInsertion
import GroupApproximation.GGT.VanKampen.DartExpansionInternal

/-! # The inserted word path is simple internally and avoids every old vertex -/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC EdgeInsertion
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure SimpleOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) extends Output D Delta f k word where
  internal_fresh : ∀ i : Fin darts.length, 0 < i.val →
    diagram.toCombMap.vertexOf (darts.get i) ∉ Set.range vertices
  internal_vertex_eq_iff : ∀ i j : Fin darts.length, 0 < i.val → 0 < j.val →
    (diagram.toCombMap.vertexOf (darts.get i) = diagram.toCombMap.vertexOf (darts.get j) ↔ i = j)
  edge_eq_iff : ∀ i j : Fin darts.length,
    diagram.toCombMap.edgeOf (darts.get i) = diagram.toCombMap.edgeOf (darts.get j) ↔ i = j

theorem exists_simple_output (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    Nonempty (SimpleOutput D Delta f k word) := by
  let letter : RelLetter G Lambda := .base (RelLetter.listVal word)
  let Xi := GFaceEdgeInsertion.diagram Delta f k hf hcells letter hvalue
  let p : Xi.toCombMap.Dart := some none
  obtain ⟨R⟩ := GEdgeWordSubdivision.exists_output D hsymm word hne hword Xi p
    (GFaceEdgeInsertion.inserted_outer Delta f k hf)
    (GFaceEdgeInsertion.inserted_cells Delta f k hf hcells letter hvalue)
    (GFaceEdgeInsertion.label_away_inserted Delta f k hf hcells letter hvalue D hlabel) rfl
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
    edge_eq_iff := E.edge_eq_iff p }⟩
  intro i hi hv
  obtain ⟨v, hv⟩ := hv
  exact E.internal_fresh p i hi ⟨V.symm v, hv⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_simple_output
