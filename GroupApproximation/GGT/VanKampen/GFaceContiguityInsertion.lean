import GroupApproximation.GGT.VanKampen.GFaceWordRetention
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport

/-! # Prescribed word insertion retaining every old contiguity outside its G-face -/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- One actual insertion output simultaneously retains every old contiguity
avoiding its insertion face, with exact arc lengths and side dart lists. -/
theorem exists_contiguity_output (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (k : Fin (Delta.faceBoundary f).darts.length)
    (hf : f ≠ Delta.outerFace) (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    ∃ R : CellOutput D Delta f k word,
      ∀ (eps : ℕ) (s : Finset Delta.toCombMap.Face), f ∉ s →
        ∀ H : Contiguity D eps Delta s,
          ∃ H' : Contiguity D eps R.diagram (R.embedding.faceSet s),
            H'.source = R.cellMap.indexEquiv H.source ∧
            H'.target = H.target.map R.cellMap.indexEquiv ∧
            H'.sourceArc.length = H.sourceArc.length ∧
            H'.targetArc.length = H.targetArc.length ∧
            H'.rightSide = H.rightSide.map R.embedding.darts ∧
            H'.leftSide = H.leftSide.map R.embedding.darts ∧
            H'.boundary.cycle = H.boundary.cycle.map R.embedding.darts := by
  obtain ⟨R⟩ := exists_cell_output D hsymm Delta hlabel f k hf hcells word hne hword hvalue
  refine ⟨R, ?_⟩
  intro eps s hs H
  refine ⟨R.embedding.contiguity R.cellMap hcells hf hs H, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · exact R.embedding.contiguity_source_length R.cellMap hcells hf hs H
  · exact R.embedding.contiguity_target_length R.cellMap hcells hf hs H

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_contiguity_output
