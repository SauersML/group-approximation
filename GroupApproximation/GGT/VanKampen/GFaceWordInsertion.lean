import GroupApproximation.GGT.VanKampen.GFaceInsertionDart
import GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision
import GroupApproximation.GGT.VanKampen.DartExpansionVertices

/-!
# Insert an actual prescribed nonempty path across a G-face

The connector reads the exact admissible relative word and has exactly that
length. Both endpoints are the prescribed old corners under an injective
vertex map. The output disc is planar and O-equivalent, with the same exterior
word and ordered relator data and one additional face.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC EdgeInsertion
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure Output (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) where
  diagram : DiscDiagram.{u, w, v} W
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  cells : Surgery.OrderedRCellTransport Delta diagram
  vertices : Delta.toCombMap.Vertex ↪ diagram.toCombMap.Vertex
  darts : List diagram.toCombMap.Dart
  nonempty : darts ≠ []
  nodup : darts.Nodup
  chain : darts.IsChain (fun d e => diagram.toCombMap.vertexOf (diagram.toCombMap.alpha d) = diagram.toCombMap.vertexOf e)
  word_eq : darts.map diagram.label = word
  initial : diagram.toCombMap.vertexOf (darts.head nonempty) =
    vertices (Delta.toCombMap.vertexOf (firstCorner Delta.toCombMap (Delta.faceBoundary f)))
  terminal : diagram.toCombMap.vertexOf (diagram.toCombMap.alpha (darts.getLast nonempty)) =
    vertices (Delta.toCombMap.vertexOf (secondCorner Delta.toCombMap (Delta.faceBoundary f) k))
  label_admissible : ∀ d, D.IsLetter (diagram.label d)
  faceCount_eq : diagram.toCombMap.faceCount = Delta.toCombMap.faceCount + 1

theorem exists_output (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    Nonempty (Output D Delta f k word) := by
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
  exact ⟨{
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
      (GFaceEdgeInsertion.faceCount_eq Delta f k hf hcells letter hvalue) }⟩

namespace Output

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
  {f : Delta.toCombMap.Face} {k : Fin (Delta.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)} (R : Output D Delta f k word)

def replacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨R.diagram, R.boundaryWord_eq, R.cells⟩

theorem length_eq : R.darts.length = word.length := by
  simpa only [List.length_map] using congrArg List.length R.word_eq

theorem reduced (hred : Delta.Reduced) : R.diagram.Reduced := R.cells.reduced hred

end Output
end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_output
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.Output.length_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.Output.reduced
