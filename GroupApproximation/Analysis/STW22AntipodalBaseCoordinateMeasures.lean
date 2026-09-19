import GroupApproximation.Analysis.STW22AntipodalBlockTraceMeasure
import GroupApproximation.Analysis.STW22BaseUniformTracialGauge

/-!
# Coordinate measures of a trace on the antipodal base algebra

An actual trace on the unitized `c₀` sum assigns a nonnegative weight to
each coordinate corner.  Its normalized restriction is represented by the
literal projective block measure; multiplying by the corner weight gives the
unnormalized coordinate measure used in the global Bauer classification.
-/

namespace GroupApproximation
namespace STW22AntipodalBaseCoordinateMeasures

open MeasureTheory
open STW22
open STW22AntipodalBlockTraceMeasure
open STW22BaseUniformTracialGauge
open STW22ActualTraceSpaces
open UniformTracialGNSTwoGauge
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped ComplexOrder ENNReal

private theorem antipodalCounterexampleBlock_nonemptyTraceFamily :
    ∀ n, Nonempty (TracialState (AntipodalCounterexampleBlock n)) :=
  fun n => nonemptyTracialState_antipodalCounterexampleBlock n

/-- The coordinate weight specialized to the concrete antipodal block family.
This specialization keeps the concrete family explicit in downstream
statements. -/
def antipodalBaseCoordinateWeight
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : ℂ :=
  baseCoordinateWeight (D := AntipodalCounterexampleBlock) sigma n

theorem antipodalBaseCoordinateWeight_nonneg
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : 0 ≤ antipodalBaseCoordinateWeight sigma n := by
  simpa [antipodalBaseCoordinateWeight] using
    (@baseCoordinateWeight_nonneg AntipodalCounterexampleBlock _ _
      antipodalCounterexampleBlock_nonemptyTraceFamily sigma n)

/-- The normalized restriction of a concrete base trace to a nonzero
antipodal coordinate. -/
def antipodalNormalizedCoordinateTracialState
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) (hweight : antipodalBaseCoordinateWeight sigma n ≠ 0) :
    TracialState (AntipodalCounterexampleBlock n) := by
  have hweight' :
      baseCoordinateWeight (D := AntipodalCounterexampleBlock) sigma n ≠ 0 := by
    simpa [antipodalBaseCoordinateWeight] using hweight
  exact @normalizedCoordinateTracialState AntipodalCounterexampleBlock _ _
    antipodalCounterexampleBlock_nonemptyTraceFamily sigma n hweight'

theorem sum_antipodalBaseCoordinateWeight_re_le_one
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        (antipodalBaseCoordinateWeight sigma n).re ≤ 1 := by
  simpa [antipodalBaseCoordinateWeight] using
    (@sum_baseCoordinateWeight_re_le_one AntipodalCounterexampleBlock _ _
      antipodalCounterexampleBlock_nonemptyTraceFamily sigma N)

/-- The real nonnegative corner weight, bundled as an `NNReal`. -/
def baseCoordinateWeightNNReal
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : NNReal :=
  ⟨(antipodalBaseCoordinateWeight sigma n).re,
    (Complex.nonneg_iff.mp (antipodalBaseCoordinateWeight_nonneg sigma n)).1⟩

@[simp] theorem baseCoordinateWeightNNReal_coe
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) :
    (baseCoordinateWeightNNReal sigma n : Real) =
      (antipodalBaseCoordinateWeight sigma n).re := rfl

/-- The finite measure carried by one projective coordinate.  At a zero
weight corner it is zero; otherwise it is the corner weight times the
probability measure representing the normalized restriction. -/
def baseCoordinateTraceMeasure
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : Measure (RP (antipodalBlockDimension n)) := by
  by_cases h : antipodalBaseCoordinateWeight sigma n = 0
  · exact 0
  · exact (baseCoordinateWeightNNReal sigma n) •
      blockTraceMeasure (antipodalNormalizedCoordinateTracialState sigma n h)

instance baseCoordinateTraceMeasure_isFinite
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : IsFiniteMeasure (baseCoordinateTraceMeasure sigma n) := by
  unfold baseCoordinateTraceMeasure
  split <;> infer_instance

instance baseCoordinateTraceMeasure_regular
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : (baseCoordinateTraceMeasure sigma n).Regular := by
  unfold baseCoordinateTraceMeasure
  split <;> infer_instance

/-- The total mass of a coordinate measure is exactly the trace's corner
weight. -/
theorem baseCoordinateTraceMeasure_univ
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) :
    baseCoordinateTraceMeasure sigma n Set.univ =
      ENNReal.ofReal (antipodalBaseCoordinateWeight sigma n).re := by
  unfold baseCoordinateTraceMeasure
  split
  next h =>
    rw [h]
    simp
  next h =>
    rw [Measure.smul_apply, blockTraceMeasure_univ]
    rw [ENNReal.ofReal_eq_coe_nnreal
      (Complex.nonneg_iff.mp
        (antipodalBaseCoordinateWeight_nonneg sigma n)).1]
    rw [ENNReal.smul_one]
    congr

/-- The coordinate weights form a summable real sequence. -/
theorem summable_baseCoordinateWeight_re
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    Summable (fun n => (antipodalBaseCoordinateWeight sigma n).re) := by
  apply summable_of_sum_range_le (c := 1)
  · intro n
    exact (Complex.nonneg_iff.mp
      (antipodalBaseCoordinateWeight_nonneg sigma n)).1
  · intro N
    cases N with
    | zero => simp
    | succ N => exact sum_antipodalBaseCoordinateWeight_re_le_one sigma N

/-- The total finite-coordinate mass is at most one. -/
theorem tsum_baseCoordinateWeight_re_le_one
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    ∑' n, (antipodalBaseCoordinateWeight sigma n).re ≤ 1 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact (Complex.nonneg_iff.mp
      (antipodalBaseCoordinateWeight_nonneg sigma n)).1
  · intro N
    cases N with
    | zero => simp
    | succ N => exact sum_antipodalBaseCoordinateWeight_re_le_one sigma N

/-- The residual mass carried by the point at infinity. -/
def baseInfinityWeightNNReal
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) : NNReal :=
  ⟨1 - ∑' n, (antipodalBaseCoordinateWeight sigma n).re,
    sub_nonneg.mpr (tsum_baseCoordinateWeight_re_le_one sigma)⟩

@[simp] theorem baseInfinityWeightNNReal_coe
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    (baseInfinityWeightNNReal sigma : Real) =
      1 - ∑' n, (antipodalBaseCoordinateWeight sigma n).re := rfl

end

end STW22AntipodalBaseCoordinateMeasures
end GroupApproximation
