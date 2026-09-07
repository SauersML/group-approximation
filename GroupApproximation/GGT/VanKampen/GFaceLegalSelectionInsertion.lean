import GroupApproximation.GGT.VanKampen.GFaceReversibleInsertion
import GroupApproximation.GGT.VanKampen.Estimating.GeometricLegalSelection

/-!
# Legal global selections survive actual insertion away from their regions

E controls diagram-label legality; D continues to control all contiguities.
The actual insertion preserves the selected family, its weight and its
cardinality. Its output therefore remains a global optimum in the same
eligible class. No small-cancellation hypothesis is transferred to E.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D E : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

namespace CellOutput

variable {S : RealizedGeometricFamily D eps Delta}
  {f : S.diagram.toCombMap.Face} {k : Fin (S.diagram.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)} (R : CellOutput E S.diagram f k word)
  (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f) (hf : f ≠ S.diagram.outerFace)
  (havoid : ∀ a ∈ S.family, f ∉ a.1)

def retainedFamily : RealizedGeometricFamily D eps Delta where
  diagram := R.diagram
  equiv := {
    boundaryWord_eq := R.boundaryWord_eq.trans S.equiv.boundaryWord_eq
    cellIndex := S.equiv.cellIndex.trans R.cells.indexEquiv
    cellWord_eq := fun i => (R.cells.cellWord_eq (S.equiv.cellIndex i)).trans
      (S.equiv.cellWord_eq i) }
  reduced := R.cells.reduced S.reduced
  family := R.embedding.geometricFamily R.cellMap hcells hf S.family havoid
  pairwise := R.embedding.geometricFamily_pairwise R.cellMap hcells hf S.family havoid S.pairwise

theorem retainedFamily_weight : (R.retainedFamily hcells hf havoid).weight = S.weight :=
  R.embedding.geometricFamily_weight R.cellMap hcells hf S.family havoid

theorem retainedFamily_card : (R.retainedFamily hcells hf havoid).family.card = S.family.card :=
  R.embedding.geometricFamily_card R.cellMap hcells hf S.family havoid

theorem retainedFamily_legal : (R.retainedFamily hcells hf havoid).LabelLegal E :=
  R.label_admissible

end CellOutput

/-- Both comparisons survive because the actual inserted family has exactly
the same weight and cardinality, and its surrounding labels remain legal. -/
def retainedOptimum (S : LegallyDistinguishedGeometricFamily D E eps Delta)
    {f : S.diagram.toCombMap.Face} {k : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)} (R : CellOutput E S.diagram f k word)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    LegallyDistinguishedGeometricFamily D E eps Delta where
  toRealizedGeometricFamily := R.retainedFamily hcells hf havoid
  label_admissible := R.retainedFamily_legal hcells hf havoid
  weight_maximal other hother := by
    rw [R.retainedFamily_weight]
    exact S.weight_maximal other hother
  card_minimal other hother heq := by
    rw [R.retainedFamily_card]
    apply S.card_minimal other hother
    exact heq.trans (R.retainedFamily_weight hcells hf havoid)

/-- Produce the insertion in the legal class at an arbitrary original base.
The old family still uses D, and the newly prescribed connector is inserted
literally with its original spelling. -/
theorem exists_preserving_legal_optimum
    (S : LegallyDistinguishedGeometricFamily D (symmetricLabelAlphabet D) eps Delta)
    (f : S.diagram.toCombMap.Face) (k : Fin (S.diagram.faceBoundary f).darts.length)
    (hf : f ≠ S.diagram.outerFace)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f)
    (havoid : ∀ a ∈ S.family, f ∉ a.1)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : RelWord.IsAdmissible D word)
    (hvalue : RelLetter.listVal word =
      RelLetter.listVal (((S.diagram.faceBoundary f).darts.take k.val).map S.diagram.label)) :
    ∃ R : CellOutput (symmetricLabelAlphabet D) S.diagram f k word,
      (retainedOptimum S R hcells hf havoid).diagram = R.diagram ∧
      (retainedOptimum S R hcells hf havoid).toRealizedGeometricFamily.weight =
        S.toRealizedGeometricFamily.weight ∧
      (retainedOptimum S R hcells hf havoid).family.card = S.family.card := by
  obtain ⟨R⟩ := exists_cell_output (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) S.diagram S.label_admissible f k hf hcells word hne
    (symmetricLabelAlphabet.admissible D hword) hvalue
  exact ⟨R, rfl, R.retainedFamily_weight hcells hf havoid,
    R.retainedFamily_card hcells hf havoid⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CellOutput.retainedFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CellOutput.retainedFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.retainedOptimum
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_preserving_legal_optimum
