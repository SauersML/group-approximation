import GroupApproximation.GGT.VanKampen.GFaceCornerInsertion
import GroupApproximation.GGT.VanKampen.Estimating.RegionLegalSelection
import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidateTransport

/-!
# Preserve unrestricted region selection through actual corner insertion

Both arcs of a self-contiguity remain represented. The actual prescribed-word
insertion retains the complete family, cardinality, weight and legal global
optimality. The construction uses no distinct-cell O52 premise.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open HullSC Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D E : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

namespace CornerOutput

variable {S : RealizedRegionFamily D eps Delta}
  {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
  {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
  {start finish : Fin (S.diagram.faceBoundary f).darts.length}
  {word : List (RelLetter G Lambda)}
  (R : CornerOutput E S.diagram f hf hcells start finish word)
  (havoid : ∀ a ∈ S.family, f ∉ a.1)

def retainedRegionRealization : RealizedRegionFamily D eps Delta where
  diagram := R.diagram
  equiv := {
    boundaryWord_eq := (boundaryWord_original R).trans S.equiv.boundaryWord_eq
    cellIndex := S.equiv.cellIndex.trans (originalCellMap R).orderedTransport.indexEquiv
    cellWord_eq := fun i => ((originalCellMap R).orderedTransport.cellWord_eq
      (S.equiv.cellIndex i)).trans (S.equiv.cellWord_eq i) }
  reduced := (originalCellMap R).orderedTransport.reduced S.reduced
  family := (originalEmbedding R).regionFamily (originalCellMap R) hcells hf S.family havoid
  pairwise := (originalEmbedding R).regionFamily_pairwise (originalCellMap R)
    hcells hf S.family havoid S.pairwise

theorem retainedRegion_weight : (retainedRegionRealization R havoid).weight = S.weight :=
  (originalEmbedding R).regionFamily_weight (originalCellMap R) hcells hf S.family havoid

theorem retainedRegion_card : (retainedRegionRealization R havoid).family.card = S.family.card :=
  (originalEmbedding R).regionFamily_card (originalCellMap R) hcells hf S.family havoid

theorem retainedRegion_legal : (retainedRegionRealization R havoid).LabelLegal E := R.label_admissible

end CornerOutput

def retainedCornerRegionOptimum (S : LegallyDistinguishedRegionFamily D E eps Delta)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput E S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    LegallyDistinguishedRegionFamily D E eps Delta where
  toRealizedRegionFamily := CornerOutput.retainedRegionRealization R havoid
  label_admissible := CornerOutput.retainedRegion_legal R havoid
  weight_maximal other hother := by
    rw [CornerOutput.retainedRegion_weight]
    exact S.weight_maximal other hother
  card_minimal other hother heq := by
    rw [CornerOutput.retainedRegion_card]
    apply S.card_minimal other hother
    exact heq.trans (CornerOutput.retainedRegion_weight R havoid)

/-- Construct an actual insertion at prescribed original endpoints. Its
legality uses the auxiliary alphabet; all selected contiguities retain D. -/
theorem exists_corner_preserving_region_optimum
    (S : LegallyDistinguishedRegionFamily D (symmetricLabelAlphabet D) eps Delta)
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
      (retainedCornerRegionOptimum S R havoid).diagram = R.diagram ∧
      (retainedCornerRegionOptimum S R havoid).toRealizedRegionFamily.weight =
        S.toRealizedRegionFamily.weight ∧
      (retainedCornerRegionOptimum S R havoid).family.card = S.family.card := by
  have hword' := symmetricLabelAlphabet.admissible D hword
  obtain ⟨R⟩ := exists_corner_output (symmetricLabelAlphabet D) S.diagram S.label_admissible
    f hf hcells start finish word hne hword'
    (fun l hl => isLetter_relWordInv _ (symmetricLabelAlphabet.symmetric D) (hword' l hl)) hvalue
  exact ⟨R, rfl, CornerOutput.retainedRegion_weight R havoid, CornerOutput.retainedRegion_card R havoid⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retainedRegion_weight
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retainedRegion_card
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.retainedCornerRegionOptimum
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_corner_preserving_region_optimum
