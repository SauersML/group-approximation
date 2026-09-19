import GroupApproximation.Analysis.STW22AntipodalTraceSimplexIntegration
import GroupApproximation.Analysis.STW22AntipodalTraceMeasureInverse
import GroupApproximation.Analysis.STW22AntipodalBoundaryMeasureRoundTrip
import GroupApproximation.Analysis.STW22BauerSimplexImage
import GroupApproximation.Analysis.STW22ProbabilitySimplexChoquet
import GroupApproximation.Analysis.STW22AntipodalTraceBoundaryTopology
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Metrizable.Basic

/-!
# The actual weak-star Bauer trace simplex of the STW XXII algebra

This file identifies the literal pointwise weak-star evaluation range of all
tracial states with the image of the boundary probability simplex.  It then
transports the full Choquet--Bauer property and computes the extreme boundary.
-/

namespace GroupApproximation
namespace STW22AntipodalTraceSimplexBauer

open MeasureTheory Set TopologicalSpace
open STW22
open STW22ActualTraceSpaces
open STW22AntipodalTraceBoundary
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalBoundaryMeasureTrace
open STW22AntipodalBaseBoundaryMeasure
open STW22AntipodalTraceMeasureInverse
open STW22AntipodalBoundaryMeasureRoundTrip
open STW22AntipodalTraceSimplexIntegration
open STW22AntipodalTraceBoundaryTopology

noncomputable section

open scoped NNReal

abbrev AntipodalBase := BaseAlgebra AntipodalCounterexampleBlock

/-- The actual trace simplex in its literal weak-star ambient function space. -/
def antipodalWeakStarTraceSimplex : Set (AntipodalBase → ℂ) :=
  Set.range (tracialStateEvaluation (A := AntipodalBase))

@[simp] theorem boundaryFiniteMeasureEvaluation_probability
    (mu : ProbabilityMeasure AntipodalTraceBoundary) :
    boundaryFiniteMeasureEvaluation mu.toFiniteMeasure =
      tracialStateEvaluation (boundaryProbabilityMeasureTracialState mu) := rfl

/-- Integration is injective on boundary probability measures, because the
explicit trace-to-measure reconstruction is a left inverse. -/
theorem boundaryFiniteMeasureEvaluation_probability_injective :
    Function.Injective (fun mu : ProbabilityMeasure AntipodalTraceBoundary ↦
      boundaryFiniteMeasureEvaluation mu.toFiniteMeasure) := by
  intro mu nu h
  have htrace : boundaryProbabilityMeasureTracialState mu =
      boundaryProbabilityMeasureTracialState nu :=
    tracialStateEvaluation_injective (by simpa using h)
  calc
    mu = baseTraceBoundaryProbabilityMeasure
        (boundaryProbabilityMeasureTracialState mu) :=
      (baseTraceBoundaryProbabilityMeasure_boundaryProbabilityMeasureTracialState mu).symm
    _ = baseTraceBoundaryProbabilityMeasure
        (boundaryProbabilityMeasureTracialState nu) := congrArg _ htrace
    _ = nu :=
      baseTraceBoundaryProbabilityMeasure_boundaryProbabilityMeasureTracialState nu

private theorem boundaryFiniteMeasureEvaluation_one
    (mu : FiniteMeasure AntipodalTraceBoundary) :
    boundaryFiniteMeasureEvaluation mu (1 : AntipodalBase) = (mu.mass : ℂ) := by
  rw [boundaryFiniteMeasureEvaluation_apply, boundaryTraceFunction_one]
  change (∫ _ : AntipodalTraceBoundary, (1 : ℂ)
      ∂(mu : Measure AntipodalTraceBoundary)) = (mu.mass : ℂ)
  rw [integral_const]
  simp only [FiniteMeasure.mass, MeasureTheory.Measure.real]
  rw [Algebra.smul_def, mul_one]
  norm_cast

/-- The finite-measure integration map is injective.  Equality first recovers
the total mass from the unit; nonzero measures are then reduced to probability
measures by Mathlib's canonical normalization. -/
theorem boundaryFiniteMeasureEvaluation_injective :
    Function.Injective boundaryFiniteMeasureEvaluation := by
  intro mu nu h
  have hmassComplex : (mu.mass : ℂ) = (nu.mass : ℂ) := by
    rw [← boundaryFiniteMeasureEvaluation_one mu,
      ← boundaryFiniteMeasureEvaluation_one nu]
    exact congrFun h 1
  have hmass : mu.mass = nu.mass := by
    exact_mod_cast hmassComplex
  by_cases hz : mu.mass = 0
  · exact (FiniteMeasure.mass_zero_iff mu).mp hz |>.trans
      ((FiniteMeasure.mass_zero_iff nu).mp (hmass.symm.trans hz)).symm
  · have hscaled :
        mu.mass • boundaryFiniteMeasureEvaluation mu.normalize.toFiniteMeasure =
          mu.mass • boundaryFiniteMeasureEvaluation nu.normalize.toFiniteMeasure := by
      rw [← boundaryFiniteMeasureEvaluation_smul,
        ← boundaryFiniteMeasureEvaluation_smul,
        ← mu.self_eq_mass_smul_normalize,
        hmass, ← nu.self_eq_mass_smul_normalize]
      exact h
    have hnormalized :
        boundaryFiniteMeasureEvaluation mu.normalize.toFiniteMeasure =
          boundaryFiniteMeasureEvaluation nu.normalize.toFiniteMeasure := by
      have hcancel := congrArg
        (fun f : AntipodalBase → ℂ ↦ mu.mass⁻¹ • f) hscaled
      simpa [← smul_assoc, inv_mul_cancel₀ hz] using hcancel
    have hprob : mu.normalize = nu.normalize :=
      boundaryFiniteMeasureEvaluation_probability_injective hnormalized
    rw [mu.self_eq_mass_smul_normalize,
      nu.self_eq_mass_smul_normalize, hmass, hprob]

/-- The probability-measure image is exactly the full weak-star trace simplex. -/
theorem boundaryFiniteMeasureEvaluation_image_probSimplex :
    boundaryFiniteMeasureEvaluation '' probSimplex AntipodalTraceBoundary =
      antipodalWeakStarTraceSimplex := by
  ext f
  constructor
  · rintro ⟨mu, hmu, rfl⟩
    have hmu' : mu ∈ Set.range
        (fun nu : ProbabilityMeasure AntipodalTraceBoundary ↦
          nu.toFiniteMeasure) := by
      rw [ProbabilityMeasure.range_toFiniteMeasure]
      exact hmu
    obtain ⟨nu, rfl⟩ := hmu'
    exact ⟨boundaryProbabilityMeasureTracialState nu, rfl⟩
  · rintro ⟨tau, rfl⟩
    let mu := baseTraceBoundaryProbabilityMeasure tau
    refine ⟨mu.toFiniteMeasure, ProbabilityMeasure.mass_toFiniteMeasure mu, ?_⟩
    rw [boundaryFiniteMeasureEvaluation_probability,
      boundaryProbabilityMeasureTracialState_baseTraceBoundaryProbabilityMeasure]

/-- The actual pointwise weak-star trace simplex is a Bauer simplex. -/
theorem isBauerSimplex_antipodalWeakStarTraceSimplex :
    IsBauerSimplex ℝ≥0 antipodalWeakStarTraceSimplex := by
  rw [← boundaryFiniteMeasureEvaluation_image_probSimplex]
  exact (isBauerSimplex_probSimplex_unconditional
    (K := AntipodalTraceBoundary)).image
      boundaryFiniteMeasureEvaluation
      continuous_boundaryFiniteMeasureEvaluation
      boundaryFiniteMeasureEvaluation_injective
      boundaryFiniteMeasureEvaluation_add
      boundaryFiniteMeasureEvaluation_smul

private theorem boundaryFiniteMeasureEvaluation_dirac
    (z : AntipodalTraceBoundary) :
    boundaryFiniteMeasureEvaluation (diracFM z) =
      tracialStateEvaluation (boundaryBaseTracialState z) := by
  funext a
  change (∫ y, boundaryTraceFunction a y ∂Measure.dirac z) =
    boundaryBaseTracialState z a
  rw [integral_dirac, boundaryTraceFunction_eq_boundaryBaseTracialState]

/-- The extreme boundary is exactly the concrete family of boundary evaluation
traces. -/
theorem extremePoints_antipodalWeakStarTraceSimplex :
    antipodalWeakStarTraceSimplex.extremePoints ℝ≥0 =
      Set.range (fun z : AntipodalTraceBoundary ↦
        tracialStateEvaluation (boundaryBaseTracialState z)) := by
  rw [← boundaryFiniteMeasureEvaluation_image_probSimplex,
    extremePoints_probSimplex_image
      boundaryFiniteMeasureEvaluation
      boundaryFiniteMeasureEvaluation_injective
      boundaryFiniteMeasureEvaluation_add
      boundaryFiniteMeasureEvaluation_smul]
  ext f
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (boundaryFiniteMeasureEvaluation_dirac z).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, boundaryFiniteMeasureEvaluation_dirac z⟩

/-- The concrete parametrization of the extreme traces. -/
def boundaryTraceEvaluationMap
    (z : AntipodalTraceBoundary) : AntipodalBase → ℂ :=
  tracialStateEvaluation (boundaryBaseTracialState z)

/-- The concrete extreme-trace parametrization is weak-star continuous. -/
theorem continuous_boundaryTraceEvaluationMap :
    Continuous boundaryTraceEvaluationMap := by
  apply continuous_pi
  intro a
  have hfun : (fun z : AntipodalTraceBoundary ↦
      boundaryTraceEvaluationMap z a) =
      (fun z : AntipodalTraceBoundary ↦ boundaryTraceFunction a z) := by
    funext z
    exact (boundaryTraceFunction_eq_boundaryBaseTracialState a z).symm
  rw [hfun]
  exact (boundaryTraceFunction a).continuous

/-- Distinct boundary points define distinct extreme traces. -/
theorem boundaryTraceEvaluationMap_injective :
    Function.Injective boundaryTraceEvaluationMap := by
  intro x y hxy
  have hmeasure : diracFM x = diracFM y :=
    boundaryFiniteMeasureEvaluation_injective (by
      rw [boundaryFiniteMeasureEvaluation_dirac,
        boundaryFiniteMeasureEvaluation_dirac]
      exact hxy)
  exact (isEmbedding_diracFM (K := AntipodalTraceBoundary)).injective hmeasure

/-- The boundary parametrization is a topological embedding. -/
theorem isEmbedding_boundaryTraceEvaluationMap :
    Topology.IsEmbedding boundaryTraceEvaluationMap :=
  (continuous_boundaryTraceEvaluationMap.isClosedEmbedding
    boundaryTraceEvaluationMap_injective).isEmbedding

/-- The actual extreme-boundary subtype of the weak-star trace simplex. -/
abbrev AntipodalWeakStarExtremeBoundary :=
  {f : AntipodalBase → ℂ //
    f ∈ antipodalWeakStarTraceSimplex.extremePoints ℝ≥0}

/-- The concrete boundary is homeomorphic to the actual extreme-boundary
subtype, with its inherited weak-star topology. -/
def boundaryHomeomorphWeakStarExtremeBoundary :
    AntipodalTraceBoundary ≃ₜ AntipodalWeakStarExtremeBoundary :=
  isEmbedding_boundaryTraceEvaluationMap.toHomeomorph.trans
    (Homeomorph.setCongr extremePoints_antipodalWeakStarTraceSimplex.symm)

/-- Compactness of the actual extreme-boundary subtype. -/
instance antipodalWeakStarExtremeBoundaryCompactSpace :
    CompactSpace AntipodalWeakStarExtremeBoundary :=
  boundaryHomeomorphWeakStarExtremeBoundary.compactSpace

/-- Metrizability of the actual extreme-boundary subtype. -/
instance antipodalWeakStarExtremeBoundaryMetrizableSpace :
    MetrizableSpace AntipodalWeakStarExtremeBoundary :=
  boundaryHomeomorphWeakStarExtremeBoundary.symm.isEmbedding.metrizableSpace

/-- Binder-free topological regularity of the actual extreme boundary. -/
theorem antipodalWeakStarExtremeBoundary_compact_metrizable :
    CompactSpace AntipodalWeakStarExtremeBoundary ∧
      MetrizableSpace AntipodalWeakStarExtremeBoundary :=
  ⟨inferInstance, inferInstance⟩

#audit_closed_axioms boundaryFiniteMeasureEvaluation_probability_injective
#audit_closed_axioms boundaryFiniteMeasureEvaluation_injective
#audit_closed_axioms boundaryFiniteMeasureEvaluation_image_probSimplex
#audit_closed_axioms isBauerSimplex_antipodalWeakStarTraceSimplex
#audit_closed_axioms extremePoints_antipodalWeakStarTraceSimplex
#audit_closed_axioms isEmbedding_boundaryTraceEvaluationMap
#audit_closed_axioms boundaryHomeomorphWeakStarExtremeBoundary
#audit_closed_axioms antipodalWeakStarExtremeBoundary_compact_metrizable

end

end STW22AntipodalTraceSimplexBauer
end GroupApproximation
