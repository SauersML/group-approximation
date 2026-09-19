import GroupApproximation.Analysis.STW22AntipodalFiniteBoundaryMeasure
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary-measure round trip

The boundary probability measure reconstructed from the trace obtained by
integration is the original probability measure.  Together with the opposite
round trip this gives the literal trace-space/probability-measure equivalence.
-/

namespace GroupApproximation
namespace STW22AntipodalBoundaryMeasureRoundTrip

open MeasureTheory Set
open STW22
open STW22AntipodalTraceBoundary
open STW22AntipodalBaseCoordinateMeasures
open STW22AntipodalBaseBoundaryMeasure
open STW22AntipodalBoundaryMeasureTrace
open STW22AntipodalBoundaryComponents
open STW22AntipodalFiniteBoundaryMeasure

noncomputable section

open scoped ENNReal OnePoint

private theorem measure_finite_add_infty
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    (mu : Measure AntipodalTraceBoundary) finiteBoundarySet +
        (mu : Measure AntipodalTraceBoundary) {(∞ : AntipodalTraceBoundary)} = 1 := by
  rw [← measure_union]
  · rw [show finiteBoundarySet ∪ {(∞ : AntipodalTraceBoundary)} = Set.univ by
      rw [← finiteBoundarySet_compl, union_compl_self]]
    exact measure_univ
  · rw [← finiteBoundarySet_compl]
    exact disjoint_compl_right
  · exact MeasurableSet.singleton _

private theorem infinityCoefficient_eq
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    ((baseInfinityWeightNNReal
      (boundaryProbabilityMeasureTracialState mu) : NNReal) : ENNReal) =
      (mu : Measure AntipodalTraceBoundary) {(∞ : AntipodalTraceBoundary)} := by
  have hbase := baseTraceBoundaryMeasure_univ
    (boundaryProbabilityMeasureTracialState mu)
  rw [baseTraceBoundaryMeasure, Measure.add_apply,
    finiteBoundaryTraceMeasure_boundaryProbabilityMeasureTracialState,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, ENNReal.smul_one] at hbase
  have heq := hbase.trans (measure_finite_add_infty mu).symm
  have hfinite :
      (mu : Measure AntipodalTraceBoundary) finiteBoundarySet ≠
        (⊤ : ENNReal) := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      (mu : Measure AntipodalTraceBoundary) finiteBoundarySet ≤
          (mu : Measure AntipodalTraceBoundary) Set.univ :=
        measure_mono (Set.subset_univ finiteBoundarySet)
      _ = 1 := measure_univ
  apply le_antisymm
  · exact (ENNReal.add_le_add_iff_left hfinite).mp heq.le
  · exact (ENNReal.add_le_add_iff_left hfinite).mp heq.ge

private theorem infinityPart_eq_restrict
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    (baseInfinityWeightNNReal (boundaryProbabilityMeasureTracialState mu)) •
        Measure.dirac (∞ : AntipodalTraceBoundary) =
      (mu : Measure AntipodalTraceBoundary).restrict
        {(∞ : AntipodalTraceBoundary)} := by
  apply Measure.ext
  intro E hE
  rw [Measure.smul_apply, Measure.restrict_apply hE,
    Measure.dirac_apply' _ hE]
  by_cases hinfty : (∞ : AntipodalTraceBoundary) ∈ E
  · rw [Set.indicator_of_mem hinfty, Pi.one_apply, ENNReal.smul_one,
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hinfty),
      infinityCoefficient_eq]
  · rw [Set.indicator_of_notMem hinfty, smul_zero]
    have hinter : E ∩ {(∞ : AntipodalTraceBoundary)} = ∅ := by
      ext z
      constructor
      · rintro ⟨hz, rfl⟩
        exact (hinfty hz).elim
      · intro hz
        exact hz.elim
    rw [hinter, measure_empty]

private theorem restrict_finite_add_infty
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    (mu : Measure AntipodalTraceBoundary).restrict finiteBoundarySet +
        (mu : Measure AntipodalTraceBoundary).restrict
          {(∞ : AntipodalTraceBoundary)} =
      (mu : Measure AntipodalTraceBoundary) := by
  rw [← Measure.restrict_union]
  · rw [show finiteBoundarySet ∪ {(∞ : AntipodalTraceBoundary)} = Set.univ by
      rw [← finiteBoundarySet_compl, union_compl_self], Measure.restrict_univ]
  · rw [← finiteBoundarySet_compl]
    exact disjoint_compl_right
  · exact MeasurableSet.singleton _

/-- The reconstructed boundary probability measure is exactly the original
one. -/
theorem baseTraceBoundaryProbabilityMeasure_boundaryProbabilityMeasureTracialState
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    baseTraceBoundaryProbabilityMeasure
        (boundaryProbabilityMeasureTracialState mu) = mu := by
  apply ProbabilityMeasure.toMeasure_injective
  change baseTraceBoundaryMeasure (boundaryProbabilityMeasureTracialState mu) =
    (mu : Measure AntipodalTraceBoundary)
  rw [baseTraceBoundaryMeasure,
    finiteBoundaryTraceMeasure_boundaryProbabilityMeasureTracialState,
    infinityPart_eq_restrict, restrict_finite_add_infty]

/-- Binder-free statement of the measure-to-trace-to-measure inverse law. -/
theorem boundaryMeasureRoundTrip_unconditional :
    Function.LeftInverse baseTraceBoundaryProbabilityMeasure
      boundaryProbabilityMeasureTracialState :=
  baseTraceBoundaryProbabilityMeasure_boundaryProbabilityMeasureTracialState

#audit_closed_axioms boundaryMeasureRoundTrip_unconditional

end

end STW22AntipodalBoundaryMeasureRoundTrip
end GroupApproximation
