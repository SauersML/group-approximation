import GroupApproximation.GGT.VanKampen.GFaceRebase
import GroupApproximation.GGT.VanKampen.GFaceReversibleInsertion

/-!
# Actual word insertion between prescribed original G-face corners

Rebase the chosen G-face at the first corner, then apply the constructed
prefix insertion at its forward cyclic offset to the second corner. The
full insertion output retains the simple path, fresh internal vertices,
ordered cell map and embedding; the lemmas below express these against the
original diagram rather than its rebased traversal.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded EdgeInsertion
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

abbrev CornerOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (start finish : Fin (Delta.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) :=
  CellOutput D (GFaceRebase.diagram Delta f start.val hf hcells) f
    (GFaceRebase.cornerIndex Delta f hf hcells start finish) word

theorem exists_corner_output (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
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
    Nonempty (CornerOutput D Delta f hf hcells start finish word) := by
  apply exists_cell_output_of_reversible D
    (GFaceRebase.diagram Delta f start.val hf hcells) hlabel f
    (GFaceRebase.cornerIndex Delta f hf hcells start finish) hf hcells word hne hword hinv
  simpa only [GFaceRebase.diagram, GFaceRebase.boundary, ite_true, GFaceRebase.cornerIndex,
    FaceBoundary.rotate] using hvalue

namespace CornerOutput

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
  {f : Delta.toCombMap.Face} {hf : f ≠ Delta.outerFace}
  {hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f}
  {start finish : Fin (Delta.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)} (R : CornerOutput D Delta f hf hcells start finish word)

theorem initial_original : R.diagram.toCombMap.vertexOf (R.darts.head R.nonempty) =
    R.vertices (Delta.toCombMap.vertexOf ((Delta.faceBoundary f).darts.get start)) := by
  have hcorner : firstCorner (GFaceRebase.diagram Delta f start.val hf hcells).toCombMap
      ((GFaceRebase.diagram Delta f start.val hf hcells).faceBoundary f) =
        (Delta.faceBoundary f).darts.get start := by
    simpa only [firstCorner, List.get_eq_getElem, List.head_eq_getElem] using
      GFaceRebase.initial_dart Delta f hf hcells start
  exact R.initial.trans (congrArg (fun d => R.vertices (Delta.toCombMap.vertexOf d)) hcorner)

theorem terminal_original :
    R.diagram.toCombMap.vertexOf (R.diagram.toCombMap.alpha (R.darts.getLast R.nonempty)) =
      R.vertices (Delta.toCombMap.vertexOf ((Delta.faceBoundary f).darts.get finish)) := by
  exact R.terminal.trans (congrArg (fun d => R.vertices (Delta.toCombMap.vertexOf d))
    (GFaceRebase.terminal_dart Delta f hf hcells start finish))

theorem boundaryWord_original : R.diagram.boundaryWord = Delta.boundaryWord :=
  R.boundaryWord_eq.trans (GFaceRebase.boundaryWord_eq Delta f start.val hf hcells)

/-- The rebasing leaves the cell records literally unchanged. -/
def originalCellMap : Surgery.OrderedRCellMap Delta R.diagram R.embedding.faces where
  cell := R.cellMap.cell
  face_eq := R.cellMap.face_eq
  word_eq := R.cellMap.word_eq
  conjugator_eq := R.cellMap.conjugator_eq
  reversed_eq := R.cellMap.reversed_eq
  list_eq := R.cellMap.list_eq

/-- Express the actual insertion embedding against the original traversals
of all other faces. Its dart and face functions are unchanged. -/
def originalEmbedding : DiscEmbeddingAway Delta R.diagram f where
  darts := R.embedding.darts
  faces := R.embedding.faces
  alpha := R.embedding.alpha
  label := R.embedding.label
  outer := R.embedding.outer
  face_boundary g hg := by
    have h := R.embedding.face_boundary g hg
    change (R.diagram.faceBoundary (R.embedding.faces g)).darts =
      (GFaceRebase.boundary Delta f start.val g).darts.map R.embedding.darts at h
    rw [GFaceRebase.boundary, if_neg hg] at h
    exact h
  facePerm := R.embedding.facePerm

noncomputable def originalReplacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨R.diagram, boundaryWord_original R, (originalCellMap R).orderedTransport⟩

theorem retained_family (metric : RelGenSet G Lambda) (eps : ℕ)
    (family : Finset (GeometricCandidate metric eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1)
    (hpairwise : EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family) :
    ∃ family' : Finset (GeometricCandidate metric eps R.diagram),
      EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family' ∧
      family'.card = family.card ∧
      EstimatingSelection.familyWeight GeometricCandidate.weight family' =
        EstimatingSelection.familyWeight GeometricCandidate.weight family := by
  let E := originalEmbedding R
  let C := originalCellMap R
  exact ⟨E.geometricFamily C hcells hf family havoid,
    E.geometricFamily_pairwise C hcells hf family havoid hpairwise,
    E.geometricFamily_card C hcells hf family havoid,
    E.geometricFamily_weight C hcells hf family havoid⟩

end CornerOutput
end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_corner_output
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.initial_original
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.terminal_original
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.originalEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.originalReplacement
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retained_family
