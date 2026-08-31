import GroupApproximation.Analysis.STW22AntipodalBoundaryTraceFunction
import GroupApproximation.Analysis.STW22AntipodalBaseBoundaryMeasure

/-!
# Base traces obtained from boundary probability measures

Integrating the continuous boundary-indexed family of actual base traces gives
an actual tracial state of the scalar-tail base algebra.
-/

namespace GroupApproximation
namespace STW22AntipodalBoundaryMeasureTrace

open MeasureTheory
open STW22
open STW22ActualTraceSpaces
open STW22AntipodalTraceBoundary
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalBaseBoundaryMeasure

noncomputable section

open scoped ComplexOrder

/-- Boundary evaluation is additive in the base element. -/
theorem boundaryTraceFunction_add
    (a b : BaseAlgebra AntipodalCounterexampleBlock) :
    boundaryTraceFunction (a + b) =
      boundaryTraceFunction a + boundaryTraceFunction b := by
  apply ContinuousMap.ext
  intro z
  simp only [ContinuousMap.add_apply,
    boundaryTraceFunction_eq_boundaryBaseTracialState]
  exact (boundaryBaseTracialState z).map_add a b

/-- Boundary evaluation is complex homogeneous in the base element. -/
theorem boundaryTraceFunction_smul (c : ℂ)
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    boundaryTraceFunction (c • a) = c • boundaryTraceFunction a := by
  apply ContinuousMap.ext
  intro z
  change boundaryTraceFunction (c • a) z = c * boundaryTraceFunction a z
  simp only [boundaryTraceFunction_eq_boundaryBaseTracialState]
  exact (boundaryBaseTracialState z).map_smul c a

/-- Boundary evaluation sends the unit to the constant one function. -/
theorem boundaryTraceFunction_one :
    boundaryTraceFunction (1 : BaseAlgebra AntipodalCounterexampleBlock) = 1 := by
  apply ContinuousMap.ext
  intro z
  simp only [boundaryTraceFunction_eq_boundaryBaseTracialState,
    ContinuousMap.one_apply]
  exact (boundaryBaseTracialState z).apply_one

/-- Integrate all boundary evaluation traces against a probability measure. -/
def boundaryProbabilityMeasureTracialState
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    TracialState (BaseAlgebra AntipodalCounterexampleBlock) where
  toLinearMap :=
    { toFun := fun a ↦ ∫ z, boundaryTraceFunction a z
          ∂(mu : Measure AntipodalTraceBoundary)
      map_add' := fun a b ↦ by
        rw [boundaryTraceFunction_add]
        have ha : HasCompactSupport (boundaryTraceFunction a) :=
          HasCompactSupport.of_support_subset_isCompact isCompact_univ
            (Set.subset_univ _)
        have hb : HasCompactSupport (boundaryTraceFunction b) :=
          HasCompactSupport.of_support_subset_isCompact isCompact_univ
            (Set.subset_univ _)
        exact integral_add
          ((boundaryTraceFunction a).continuous.integrable_of_hasCompactSupport ha)
          ((boundaryTraceFunction b).continuous.integrable_of_hasCompactSupport hb)
      map_smul' := fun c a ↦ by
        rw [boundaryTraceFunction_smul]
        exact integral_smul c _ }
  map_one := by
    change (∫ z, boundaryTraceFunction
      (1 : BaseAlgebra AntipodalCounterexampleBlock) z
      ∂(mu : Measure AntipodalTraceBoundary)) = 1
    rw [boundaryTraceFunction_one]
    simp
  map_star_mul_self_nonneg := by
    intro a
    change 0 ≤ (∫ z, boundaryTraceFunction (star a * a) z
      ∂(mu : Measure AntipodalTraceBoundary))
    have hsupp : HasCompactSupport (boundaryTraceFunction (star a * a)) :=
      HasCompactSupport.of_support_subset_isCompact isCompact_univ
        (Set.subset_univ _)
    have hint : Integrable (boundaryTraceFunction (star a * a))
        (mu : Measure AntipodalTraceBoundary) :=
      (boundaryTraceFunction (star a * a)).continuous.integrable_of_hasCompactSupport
        hsupp
    rw [Complex.nonneg_iff]
    constructor
    · change 0 ≤ RCLike.re (∫ z, boundaryTraceFunction (star a * a) z
        ∂(mu : Measure AntipodalTraceBoundary))
      rw [← integral_re hint]
      exact integral_nonneg fun z ↦ by
        rw [boundaryTraceFunction_eq_boundaryBaseTracialState]
        exact (Complex.nonneg_iff.mp
          ((boundaryBaseTracialState z).map_star_mul_self_nonneg a)).1
    · change 0 = RCLike.im (∫ z, boundaryTraceFunction (star a * a) z
        ∂(mu : Measure AntipodalTraceBoundary))
      rw [← integral_im hint]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [] with z
      rw [boundaryTraceFunction_eq_boundaryBaseTracialState]
      have hz : 0 ≤ (boundaryBaseTracialState z) (star a * a) :=
        (boundaryBaseTracialState z).map_star_mul_self_nonneg a
      change ((boundaryBaseTracialState z) (star a * a)).im = 0
      exact (Complex.nonneg_iff.mp hz).2.symm
  map_mul_comm := by
    intro a b
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [boundaryTraceFunction_eq_boundaryBaseTracialState]
    exact (boundaryBaseTracialState z).map_mul_comm a b

@[simp] theorem boundaryProbabilityMeasureTracialState_apply
    (mu : ProbabilityMeasure AntipodalTraceBoundary)
    (a : BaseAlgebra AntipodalCounterexampleBlock) :
    boundaryProbabilityMeasureTracialState mu a =
      ∫ z, boundaryTraceFunction a z
        ∂(mu : Measure AntipodalTraceBoundary) := rfl

end

end STW22AntipodalBoundaryMeasureTrace
end GroupApproximation
