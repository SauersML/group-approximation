import GroupApproximation.GGT.VanKampen.SelfContiguityModel
import GroupApproximation.GGT.VanKampen.Estimating.RegionLegalSelection

/-!
# The self-contiguity contributes both arcs to actual selection

The concrete region contributes two interior darts and leaves one unbound
dart on its relator triangle. It also supplies an eligible nonzero family
for global maximization over the enlarged geometric pool.
-/

namespace GroupApproximation.GGT.VanKampen.SelfContiguityModel

open Embedded HullSC
open scoped Classical

noncomputable def candidate : RegionCandidate D 0 diagram := ⟨faces, region⟩

theorem singleton_pairwise :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible {candidate} := by
  intro b hb c hc hne
  exact (hne ((Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp hc).symm)).elim

/-- Counting either end exclusively would lose a dart in this actual model. -/
theorem both_ends_counted :
    candidate.weight = 2 ∧ (candidate.cellArcDarts 0).card = 2 := by
  refine ⟨rfl, ?_⟩
  simp only [RegionCandidate.card_cellArcDarts, candidate, region, sourceArc, targetArc, if_true]

theorem interior_count : (RegionCandidate.boundDarts {candidate} true 0).card = 2 := by
  rw [RegionCandidate.card_boundDarts {candidate} singleton_pairwise]
  have hk : RegionCandidate.ofKind {candidate} true = {candidate} := by
    simp [RegionCandidate.ofKind, candidate, region]
  rw [hk, Finset.sum_singleton]
  exact both_ends_counted.2

theorem unbound_count : (RegionCandidate.unboundDarts {candidate} 0).card = 1 := by
  have h := RegionCandidate.perimeter_eq {candidate} singleton_pairwise 0
  have hk : RegionCandidate.ofKind {candidate} false = ∅ := by
    simp [RegionCandidate.ofKind, candidate, region]
  have he : (RegionCandidate.boundDarts {candidate} false 0).card = 0 := by
    simp only [RegionCandidate.boundDarts, hk, Finset.biUnion_empty, Finset.card_empty]
  rw [he, interior_count] at h
  have hp : (cell diagram 0).word.length = 3 := rfl
  rw [hp] at h
  omega

/-- Legal global maximization compares against the actual self-contiguity
family, and its optimum retains the original finite perimeter bound. -/
theorem exists_legal_selected_weight :
    ∃ S : LegallyDistinguishedRegionFamily D (symmetricLabelAlphabet D) 0 diagram,
      2 ≤ S.toRealizedRegionFamily.weight ∧ S.toRealizedRegionFamily.weight ≤ 4 := by
  let seed : RealizedRegionFamily D 0 diagram := {
    diagram := diagram
    equiv := OEquivalentDiscDiagram.refl diagram
    reduced := positive_self_contiguity.1
    family := {candidate}
    pairwise := singleton_pairwise }
  have hlegal : seed.LabelLegal (symmetricLabelAlphabet D) := by
    intro d
    exact symmetricLabelAlphabet.isLetter D (Set.mem_univ _)
  obtain ⟨S⟩ := exists_legallyDistinguishedRegion_of_seed seed hlegal
  have hh := S.weight_maximal seed hlegal
  have hw : seed.weight = 2 := by
    simp only [RealizedRegionFamily.weight, seed, EstimatingSelection.familyWeight,
      Finset.sum_singleton, both_ends_counted.1]
  rw [hw] at hh
  refine ⟨S, hh, ?_⟩
  have hb := S.toRealizedRegionFamily.weight_le
  have hp : (∑ i : Fin diagram.rCellCount, (cell diagram i).word.length) = 3 := by
    change (∑ i : Fin 1, (cell diagram i).word.length) = 3
    rw [Fin.sum_univ_one]
    rfl
  have he : diagram.boundaryWord.length = 1 := by
    change (RelWord.revInv ((boundary (face 2)).darts.map label)).length = 1
    rw [boundary_face_darts]
    rfl
  rw [hp, he] at hb
  exact hb

end GroupApproximation.GGT.VanKampen.SelfContiguityModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.SelfContiguityModel.both_ends_counted
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SelfContiguityModel.interior_count
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SelfContiguityModel.unbound_count
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SelfContiguityModel.exists_legal_selected_weight
