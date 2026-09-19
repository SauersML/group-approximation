import GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample
import GroupApproximation.GGT.VanKampen.Estimating.GeometricGlobalSelection
import GroupApproximation.GGT.VanKampen.Estimating.GeometricExterior
import GroupApproximation.GGT.VanKampen.Estimating.GeometricIncidence

/-!
# The retained partition and global selection on the six-dart model

The two witnesses erased by the historical candidate give different actual
boundary counts. Global maximization also has a nonzero realized model,
even though it is allowed to change the G-cell subdivision.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample

open Embedded ExteriorArcCounterexample
open scoped Classical

theorem singleton_pairwise (a : GeometricCandidate D 2 diagram) :
    EstimatingSelection.PairwiseCompatible GeometricCandidate.Compatible {a} := by
  intro b hb c hc hne
  exact (hne ((Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp hc).symm)).elim

theorem singleton_exterior_card (a : GeometricCandidate D 2 diagram) (ht : a.2.target = none) :
    (GeometricCandidate.boundDarts {a} false a.2.source).card = a.2.sourceArc.length := by
  apply GeometricCandidate.card_exterior_eq {a} (singleton_pairwise a)
  · intro b hb c hc _
    exact (Finset.mem_singleton.mp (Finset.mem_filter.mp hb).1).trans
      (Finset.mem_singleton.mp (Finset.mem_filter.mp hc).1).symm
  · simp [GeometricCandidate.ofKind, ht]

theorem retained_exterior_counts :
    (GeometricCandidate.boundDarts {geometricHigh} false 0).card = 1 ∧
      (GeometricCandidate.boundDarts {geometricLow} false 0).card = 0 :=
  ⟨singleton_exterior_card geometricHigh rfl, singleton_exterior_card geometricLow rfl⟩

theorem retained_unbound_counts :
    (GeometricCandidate.unboundDarts {geometricHigh} 0).card = 2 ∧
      (GeometricCandidate.unboundDarts {geometricLow} 0).card = 3 := by
  have hh := GeometricCandidate.perimeter_eq {geometricHigh} (singleton_pairwise geometricHigh) 0
  have hl := GeometricCandidate.perimeter_eq {geometricLow} (singleton_pairwise geometricLow) 0
  have hi : GeometricCandidate.ofKind {geometricHigh} true = ∅ := by
    simp [GeometricCandidate.ofKind, geometricHigh, high, region]
  have li : GeometricCandidate.ofKind {geometricLow} true = ∅ := by
    simp [GeometricCandidate.ofKind, geometricLow, low]
  rw [retained_exterior_counts.1] at hh
  rw [retained_exterior_counts.2] at hl
  simp only [GeometricCandidate.boundDarts, hi, li, Finset.biUnion_empty, Finset.card_empty,
    Nat.add_zero] at hh hl
  have hp : (cell diagram 0).word.length = 3 := rfl
  rw [hp] at hh hl
  omega

/-- The global optimum is attained on an actual reduced O-equivalent
diagram, with nonzero retained weight bounded by the original four darts. -/
theorem exists_global_selected_weight :
    ∃ S : GloballyDistinguishedGeometricFamily D 2 diagram,
      2 ≤ S.toRealizedGeometricFamily.weight ∧ S.toRealizedGeometricFamily.weight ≤ 4 := by
  have hred : diagram.Reduced := reduced_of_rCellCount_le_one diagram (by decide)
  obtain ⟨S⟩ := exists_globallyDistinguishedGeometricFamily D 2 diagram hred
  let highFamily : RealizedGeometricFamily D 2 diagram := {
    diagram := diagram
    equiv := OEquivalentDiscDiagram.refl diagram
    reduced := hred
    family := {geometricHigh}
    pairwise := singleton_pairwise geometricHigh }
  have hh := S.weight_maximal highFamily
  have hw : highFamily.weight = 2 := by
    simp only [RealizedGeometricFamily.weight, highFamily, EstimatingSelection.familyWeight,
      Finset.sum_singleton, retained_weights.1]
  rw [hw] at hh
  refine ⟨S, hh, ?_⟩
  have hb := S.toRealizedGeometricFamily.weight_le
  have hperimeter : (∑ i : Fin diagram.rCellCount, (cell diagram i).word.length) = 3 := by
    change (∑ i : Fin 1, (cell diagram i).word.length) = 3
    rw [Fin.sum_univ_one]
    rfl
  have hboundary : diagram.boundaryWord.length = 1 := by
    rw [← dartWord_outerDarts]
    simp only [dartWord, List.length_map, outerDarts]
    change (boundary (face 2)).darts.reverse.length = 1
    rw [boundary_face_darts]
    rfl
  rw [hperimeter, hboundary] at hb
  exact hb

end GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample.retained_exterior_counts
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample.retained_unbound_counts
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.CandidateWeightCounterexample.exists_global_selected_weight
