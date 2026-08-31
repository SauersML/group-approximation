import GroupApproximation.Analysis.STW22AntipodalBaseCoordinateMeasures

/-!
# The boundary probability measure of an antipodal base trace

The coordinate projective measures are pushed into the one-point
compactification and summed.  The missing mass is placed at infinity.
-/

namespace GroupApproximation
namespace STW22AntipodalBaseBoundaryMeasure

open MeasureTheory
open STW22
open STW22AntipodalTraceBoundary
open STW22AntipodalBaseCoordinateMeasures
open STW22ActualTraceSpaces
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped ENNReal OnePoint

/-- The global boundary carries its Borel measurable structure. -/
instance antipodalTraceBoundaryMeasurableSpace :
    MeasurableSpace AntipodalTraceBoundary := borel _

instance antipodalTraceBoundaryBorelSpace :
    BorelSpace AntipodalTraceBoundary := ⟨rfl⟩

/-- Inclusion of the `n`-th projective component into the literal boundary. -/
def boundaryCoordinateEmbedding (n : Nat) :
    RP (antipodalBlockDimension n) → AntipodalTraceBoundary :=
  fun x => ((⟨n, x⟩ : Σ n : Nat, RP (antipodalBlockDimension n)) :
    AntipodalTraceBoundary)

theorem continuous_boundaryCoordinateEmbedding (n : Nat) :
    Continuous (boundaryCoordinateEmbedding n) :=
  OnePoint.continuous_coe.comp continuous_sigmaMk

theorem measurable_boundaryCoordinateEmbedding (n : Nat) :
    Measurable (boundaryCoordinateEmbedding n) :=
  (continuous_boundaryCoordinateEmbedding n).measurable

/-- One coordinate measure, pushed into the global boundary. -/
def pushedCoordinateTraceMeasure
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) : Measure AntipodalTraceBoundary :=
  Measure.map (boundaryCoordinateEmbedding n) (baseCoordinateTraceMeasure sigma n)

@[simp] theorem pushedCoordinateTraceMeasure_univ
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock))
    (n : Nat) :
    pushedCoordinateTraceMeasure sigma n Set.univ =
      ENNReal.ofReal (antipodalBaseCoordinateWeight sigma n).re := by
  rw [pushedCoordinateTraceMeasure, Measure.map_apply
    (measurable_boundaryCoordinateEmbedding n) MeasurableSet.univ,
    Set.preimage_univ, baseCoordinateTraceMeasure_univ]

/-- Sum of all finite-coordinate measures. -/
def finiteBoundaryTraceMeasure
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    Measure AntipodalTraceBoundary :=
  Measure.sum (fun n => pushedCoordinateTraceMeasure sigma n)

@[simp] theorem finiteBoundaryTraceMeasure_univ
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    finiteBoundaryTraceMeasure sigma Set.univ =
      ENNReal.ofReal (∑' n, (antipodalBaseCoordinateWeight sigma n).re) := by
  rw [finiteBoundaryTraceMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [pushedCoordinateTraceMeasure_univ]
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact fun n => (Complex.nonneg_iff.mp
      (antipodalBaseCoordinateWeight_nonneg sigma n)).1
  · exact summable_baseCoordinateWeight_re sigma

/-- The global measure: coordinate mass plus residual mass at infinity. -/
def baseTraceBoundaryMeasure
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    Measure AntipodalTraceBoundary :=
  finiteBoundaryTraceMeasure sigma +
    (baseInfinityWeightNNReal sigma) • Measure.dirac (∞ : AntipodalTraceBoundary)

/-- The assembled boundary measure has total mass one. -/
theorem baseTraceBoundaryMeasure_univ
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    baseTraceBoundaryMeasure sigma Set.univ = 1 := by
  rw [baseTraceBoundaryMeasure, Measure.add_apply, finiteBoundaryTraceMeasure_univ,
    Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ]
  rw [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, ENNReal.smul_one]
  rw [ENNReal.coe_nnreal_eq, baseInfinityWeightNNReal_coe]
  rw [← ENNReal.ofReal_add]
  · rw [show (∑' n, (antipodalBaseCoordinateWeight sigma n).re) +
        (1 - ∑' n, (antipodalBaseCoordinateWeight sigma n).re) = 1 by ring]
    exact ENNReal.ofReal_one
  · exact tsum_nonneg fun n ↦
      (Complex.nonneg_iff.mp
        (antipodalBaseCoordinateWeight_nonneg sigma n)).1
  · exact sub_nonneg.mpr (tsum_baseCoordinateWeight_re_le_one sigma)

instance baseTraceBoundaryMeasure_isProbability
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    IsProbabilityMeasure (baseTraceBoundaryMeasure sigma) :=
  ⟨baseTraceBoundaryMeasure_univ sigma⟩

/-- The assembled measure bundled in the weak-topology probability simplex. -/
def baseTraceBoundaryProbabilityMeasure
    (sigma : TracialState (BaseAlgebra AntipodalCounterexampleBlock)) :
    ProbabilityMeasure AntipodalTraceBoundary :=
  ⟨baseTraceBoundaryMeasure sigma, inferInstance⟩

end

end STW22AntipodalBaseBoundaryMeasure
end GroupApproximation
