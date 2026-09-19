import GroupApproximation.GGT.VanKampen.GFaceCornerInsertion
import GroupApproximation.GGT.VanKampen.Estimating.GeometricLegalSelection

/-! # Preserve the legal global optimum through insertion at original corners -/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D E : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

namespace CornerOutput

variable {S : RealizedGeometricFamily D eps Delta}
  {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
  {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
  {start finish : Fin (S.diagram.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)}
  (R : CornerOutput E S.diagram f hf hcells start finish word)
  (havoid : ∀ a ∈ S.family, f ∉ a.1)

def retainedRealization : RealizedGeometricFamily D eps Delta where
  diagram := R.diagram
  equiv := {
    boundaryWord_eq := (boundaryWord_original R).trans S.equiv.boundaryWord_eq
    cellIndex := S.equiv.cellIndex.trans (originalCellMap R).orderedTransport.indexEquiv
    cellWord_eq := fun i => ((originalCellMap R).orderedTransport.cellWord_eq
      (S.equiv.cellIndex i)).trans (S.equiv.cellWord_eq i) }
  reduced := (originalCellMap R).orderedTransport.reduced S.reduced
  family := (originalEmbedding R).geometricFamily (originalCellMap R) hcells hf S.family havoid
  pairwise := (originalEmbedding R).geometricFamily_pairwise (originalCellMap R)
    hcells hf S.family havoid S.pairwise

theorem retained_weight : (retainedRealization R havoid).weight = S.weight :=
  (originalEmbedding R).geometricFamily_weight (originalCellMap R) hcells hf S.family havoid

theorem retained_card : (retainedRealization R havoid).family.card = S.family.card :=
  (originalEmbedding R).geometricFamily_card (originalCellMap R) hcells hf S.family havoid

theorem retained_legal : (retainedRealization R havoid).LabelLegal E := R.label_admissible

end CornerOutput

def retainedCornerOptimum (S : LegallyDistinguishedGeometricFamily D E eps Delta)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput E S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    LegallyDistinguishedGeometricFamily D E eps Delta where
  toRealizedGeometricFamily := CornerOutput.retainedRealization R havoid
  label_admissible := CornerOutput.retained_legal R havoid
  weight_maximal other hother := by
    rw [CornerOutput.retained_weight]
    exact S.weight_maximal other hother
  card_minimal other hother heq := by
    rw [CornerOutput.retained_card]
    apply S.card_minimal other hother
    exact heq.trans (CornerOutput.retained_weight R havoid)

/-- Construct an actual insertion at prescribed original endpoints. Its
legality uses the auxiliary alphabet; all selected contiguities retain D. -/
theorem exists_corner_preserving_legal_optimum
    (S : LegallyDistinguishedGeometricFamily D (symmetricLabelAlphabet D) eps Delta)
    (f : S.diagram.toCombMap.Face) (hf : f ≠ S.diagram.outerFace)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f)
    (havoid : ∀ a ∈ S.family, f ∉ a.1)
    (start finish : Fin (S.diagram.faceBoundary f).darts.length)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : RelWord.IsAdmissible D word)
    (hvalue : RelLetter.listVal word = RelLetter.listVal
      ((((S.diagram.faceBoundary f).darts.rotate start.val).take
        ((S.diagram.faceBoundary f).forwardOffset start finish)).map S.diagram.label)) :
    ∃ R : CornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word,
      (retainedCornerOptimum S R havoid).diagram = R.diagram ∧
      (retainedCornerOptimum S R havoid).toRealizedGeometricFamily.weight =
        S.toRealizedGeometricFamily.weight ∧
      (retainedCornerOptimum S R havoid).family.card = S.family.card := by
  have hword' := symmetricLabelAlphabet.admissible D hword
  obtain ⟨R⟩ := exists_corner_output (symmetricLabelAlphabet D) S.diagram S.label_admissible
    f hf hcells start finish word hne hword'
    (fun l hl => isLetter_relWordInv _ (symmetricLabelAlphabet.symmetric D) (hword' l hl)) hvalue
  exact ⟨R, rfl, CornerOutput.retained_weight R havoid, CornerOutput.retained_card R havoid⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retained_weight
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retained_card
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.retainedCornerOptimum
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_corner_preserving_legal_optimum
