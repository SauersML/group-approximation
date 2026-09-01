import GroupApproximation.Analysis.STW22AntipodalBoundaryMeasureTrace
import GroupApproximation.Analysis.STW22ProbabilitySimplexBauer
import GroupApproximation.Meta.AxiomGuard

/-!
# The finite-measure integration map for the antipodal trace simplex

The trace simplex is realized in the literal ambient product
`BaseAlgebra AntipodalCounterexampleBlock → ℂ`.  This file constructs the
linear map from finite boundary measures into that product and proves continuity
for the actual weak topology on finite measures and the pointwise topology on
the product.
-/

namespace GroupApproximation
namespace STW22AntipodalTraceSimplexIntegration

open Filter MeasureTheory
open STW22
open STW22ActualTraceSpaces
open STW22AntipodalTraceBoundary
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalBoundaryMeasureTrace

noncomputable section

open scoped NNReal

abbrev AntipodalBase := BaseAlgebra AntipodalCounterexampleBlock

/-- Integration of the boundary evaluations against an arbitrary finite
measure, regarded as a point of the ambient weak-star product. -/
def boundaryFiniteMeasureEvaluation
    (mu : FiniteMeasure AntipodalTraceBoundary) : AntipodalBase → ℂ :=
  fun a ↦ ∫ z, boundaryTraceFunction a z ∂(mu : Measure AntipodalTraceBoundary)

@[simp] theorem boundaryFiniteMeasureEvaluation_apply
    (mu : FiniteMeasure AntipodalTraceBoundary) (a : AntipodalBase) :
    boundaryFiniteMeasureEvaluation mu a =
      ∫ z, boundaryTraceFunction a z ∂(mu : Measure AntipodalTraceBoundary) := rfl

private theorem boundaryTraceFunction_integrable
    (mu : FiniteMeasure AntipodalTraceBoundary) (a : AntipodalBase) :
    Integrable (boundaryTraceFunction a) (mu : Measure AntipodalTraceBoundary) := by
  exact (boundaryTraceFunction a).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ
      (Set.subset_univ _))

/-- The finite-measure integration map is additive. -/
theorem boundaryFiniteMeasureEvaluation_add
    (mu nu : FiniteMeasure AntipodalTraceBoundary) :
    boundaryFiniteMeasureEvaluation (mu + nu) =
      boundaryFiniteMeasureEvaluation mu + boundaryFiniteMeasureEvaluation nu := by
  funext a
  change (∫ z, boundaryTraceFunction a z
      ∂((mu + nu : FiniteMeasure AntipodalTraceBoundary) :
        Measure AntipodalTraceBoundary)) =
    (∫ z, boundaryTraceFunction a z ∂(mu : Measure AntipodalTraceBoundary)) +
      ∫ z, boundaryTraceFunction a z ∂(nu : Measure AntipodalTraceBoundary)
  rw [FiniteMeasure.toMeasure_add]
  exact integral_add_measure
    (boundaryTraceFunction_integrable mu a)
    (boundaryTraceFunction_integrable nu a)

/-- The finite-measure integration map is homogeneous over nonnegative real
scalars. -/
theorem boundaryFiniteMeasureEvaluation_smul
    (c : ℝ≥0) (mu : FiniteMeasure AntipodalTraceBoundary) :
    boundaryFiniteMeasureEvaluation (c • mu) =
      c • boundaryFiniteMeasureEvaluation mu := by
  funext a
  change (∫ z, boundaryTraceFunction a z
      ∂((c • mu : FiniteMeasure AntipodalTraceBoundary) :
        Measure AntipodalTraceBoundary)) =
    c • ∫ z, boundaryTraceFunction a z ∂(mu : Measure AntipodalTraceBoundary)
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]

/-- The integration map is continuous from weak convergence of finite measures
to pointwise convergence on the ambient trace-function space. -/
theorem continuous_boundaryFiniteMeasureEvaluation :
    Continuous boundaryFiniteMeasureEvaluation := by
  apply continuous_pi
  intro a
  rw [continuous_iff_continuousAt]
  intro mu
  let f : BoundedContinuousFunction AntipodalTraceBoundary ℂ :=
    (ContinuousMap.equivBoundedOfCompact
      AntipodalTraceBoundary ℂ) (boundaryTraceFunction a)
  exact (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
    (tendsto_id : Tendsto
      (fun nu : FiniteMeasure AntipodalTraceBoundary ↦ nu)
      (nhds mu) (nhds mu)) f

#audit_closed_axioms continuous_boundaryFiniteMeasureEvaluation

end

end STW22AntipodalTraceSimplexIntegration
end GroupApproximation
