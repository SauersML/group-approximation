import GroupApproximation.GGT.VanKampen.GFaceContiguityInsertion
import GroupApproximation.GGT.VanKampen.ReversibleSpelling

/-!
# Contiguity-preserving insertion with reversible connector spellings

Both orientations of the chosen connector are legal. This suffices for the
actual insertion and full family transport; the base alphabet need not be
inverse-closed. An arbitrary legal nonempty connector can first be respelled
with exactly the same length and path vertices. Existing boundary and
relator words retain their original relative-letter spelling.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded OsinComponents
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

theorem exists_family_output_of_reversible (D : RelGenSet G Lambda)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : RelWord.IsAdmissible D word)
    (hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l))
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    ∃ R : CellOutput D Delta f k word,
      ∀ (eps : ℕ) (family : Finset (GeometricCandidate D eps Delta)),
        (∀ a ∈ family, f ∉ a.1) →
        EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family →
        ∃ family' : Finset (GeometricCandidate D eps R.diagram),
          EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible family' ∧
          family'.card = family.card ∧
          EstimatingSelection.familyWeight GeometricCandidate.weight family' =
            EstimatingSelection.familyWeight GeometricCandidate.weight family ∧
          ∀ a ∈ family', ∃ b ∈ family, a.1 = R.embedding.faceSet b.1 := by
  obtain ⟨R⟩ := exists_cell_output_of_reversible D Delta hlabel f k hf hcells word hne hword hinv hvalue
  refine ⟨R, ?_⟩
  intro eps family havoid hcompatible
  exact ⟨R.embedding.geometricFamily R.cellMap hcells hf family havoid,
    R.embedding.geometricFamily_pairwise R.cellMap hcells hf family havoid hcompatible,
    R.embedding.geometricFamily_card R.cellMap hcells hf family havoid,
    R.embedding.geometricFamily_weight R.cellMap hcells hf family havoid,
    fun _ h => R.embedding.geometricFamily_faces R.cellMap hcells hf family havoid h⟩

/-- The new connector's spelling can be chosen reversible while keeping its
length and every group vertex. The returned actual insertion retains the
full ordered cell map and all contiguities away from the insertion face. -/
theorem exists_respelt_cell_output (D : RelGenSet G Lambda)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : RelWord.IsAdmissible D word)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    ∃ S : ReversibleSpelling D word, Nonempty (CellOutput D Delta f k S.word) := by
  obtain ⟨S⟩ := exists_reversibleSpelling D word hword
  exact ⟨S, exists_cell_output_of_reversible D Delta hlabel f k hf hcells S.word
    (S.nonempty hne) S.admissible S.inverse_admissible (S.value_eq.trans hvalue)⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_family_output_of_reversible
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_respelt_cell_output
