import GroupApproximation.Analysis.STW22AntipodalCoordinateRestriction

/-!
# Recovery of the finite part of a boundary measure

The finite-coordinate measure assembled from the trace of a boundary
probability measure is the restriction of that original measure to the
finite part of the one-point compactification.
-/

namespace GroupApproximation
namespace STW22AntipodalFiniteBoundaryMeasure

open MeasureTheory Set
open STW22
open STW22AntipodalTraceBoundary
open STW22AntipodalBaseBoundaryMeasure
open STW22AntipodalBoundaryMeasureTrace
open STW22AntipodalBoundaryComponents
open STW22AntipodalCoordinateRestriction

noncomputable section

/-- Countable additivity over the disjoint projective components identifies
the reconstructed finite-boundary measure with restriction to the finite
part. -/
theorem finiteBoundaryTraceMeasure_boundaryProbabilityMeasureTracialState
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    finiteBoundaryTraceMeasure (boundaryProbabilityMeasureTracialState mu) =
      (mu : Measure AntipodalTraceBoundary).restrict finiteBoundarySet := by
  rw [finiteBoundaryTraceMeasure]
  simp_rw [pushedCoordinateTraceMeasure_boundaryProbabilityMeasureTracialState]
  apply Measure.ext
  intro E hE
  rw [Measure.sum_apply _ hE,
    Measure.restrict_apply hE, finiteBoundarySet_eq_iUnion,
    Set.inter_iUnion]
  have hdis : Pairwise fun n m : Nat ↦
      Disjoint (E ∩ boundaryCoordinateSet n)
        (E ∩ boundaryCoordinateSet m) := by
    intro n m hnm
    exact (boundaryCoordinateSet_disjoint hnm).mono
      (Set.inter_subset_right) (Set.inter_subset_right)
  have hmeas : ∀ n : Nat,
      MeasurableSet (E ∩ boundaryCoordinateSet n) :=
    fun n ↦ hE.inter (measurableSet_boundaryCoordinateSet n)
  rw [measure_iUnion hdis hmeas]
  congr 1
  funext n
  rw [Measure.restrict_apply hE]

end

end STW22AntipodalFiniteBoundaryMeasure
end GroupApproximation
