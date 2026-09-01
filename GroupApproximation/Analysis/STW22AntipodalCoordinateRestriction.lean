import GroupApproximation.Analysis.STW22AntipodalBoundaryComponents
import GroupApproximation.Analysis.STW22AntipodalBlockComplexCenter
import GroupApproximation.Analysis.STW22AntipodalTraceMeasureInverse

/-!
# Coordinate restrictions of a boundary measure

For a probability measure on the literal antipodal boundary, integrate the
boundary traces to obtain a base trace and reconstruct its coordinate
measures.  Each pushed reconstructed coordinate measure is exactly the
restriction of the original boundary measure to that projective component.
-/

namespace GroupApproximation
namespace STW22AntipodalCoordinateRestriction

open Filter MeasureTheory Set
open STW22
open STW22ActualTraceSpaces
open STW22AntipodalTraceBoundary
open STW22AntipodalBaseCoordinateMeasures
open STW22AntipodalBaseBoundaryMeasure
open STW22AntipodalBoundaryTraceFunction
open STW22AntipodalBoundaryMeasureTrace
open STW22AntipodalBlockMeasureTrace
open STW22AntipodalBlockComplexCenter
open STW22AntipodalTraceMeasureInverse
open STW22AntipodalBoundaryComponents
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped ComplexOrder OnePoint

private def coordinateTestFunction (n : Nat)
    (h : CompactlySupportedContinuousMap AntipodalTraceBoundary Real) :
    C(RP (antipodalBlockDimension n), Complex) where
  toFun x := (h (boundaryCoordinateEmbedding n x) : Complex)
  continuous_toFun := Complex.continuous_ofReal.comp
    (h.continuous.comp (continuous_boundaryCoordinateEmbedding n))

private theorem boundaryTraceFunction_coordinateTestElement
    (n : Nat) (h : CompactlySupportedContinuousMap AntipodalTraceBoundary Real)
    (z : AntipodalTraceBoundary) :
    boundaryTraceFunction
      (antipodalBaseSummandInclusion n
        (projectiveComplexCenter (s := antipodalBlockSize n)
          (coordinateTestFunction n h))) z =
      (boundaryCoordinateSet n).indicator
        (fun w ↦ (h w : Complex)) z := by
  induction z using OnePoint.rec with
  | infty =>
      rw [boundaryTraceFunction_infty,
        infinityBaseTracialState_apply,
        baseScalarStarAlgHom_antipodalBaseSummandInclusion]
      rw [Set.indicator_of_notMem]
      rw [boundaryCoordinateSet_eq_image]
      exact OnePoint.infty_notMem_image_coe
  | coe z =>
      rcases z with ⟨m, x⟩
      rw [boundaryTraceFunction_baseSummandInclusion]
      by_cases hmn : m = n
      · subst m
        rw [dif_pos rfl, projectiveBlockTraceFunction_projectiveComplexCenter]
        rw [Set.indicator_of_mem]
        · rfl
        · exact ⟨x, rfl⟩
      · rw [dif_neg hmn, Set.indicator_of_notMem]
        rintro ⟨y, hy⟩
        have hsigma : (⟨n, y⟩ :
            Σ k : Nat, RP (antipodalBlockDimension k)) = ⟨m, x⟩ :=
          OnePoint.coe_injective hy
        exact hmn (congrArg Sigma.fst hsigma).symm

/-- Reconstructing the `n`-th coordinate measure from the trace integrated
against `mu` gives precisely `mu` restricted to that boundary component. -/
theorem pushedCoordinateTraceMeasure_boundaryProbabilityMeasureTracialState
    (mu : ProbabilityMeasure AntipodalTraceBoundary) (n : Nat) :
    pushedCoordinateTraceMeasure
        (boundaryProbabilityMeasureTracialState mu) n =
      (mu : Measure AntipodalTraceBoundary).restrict (boundaryCoordinateSet n) := by
  letI : IsFiniteMeasure (pushedCoordinateTraceMeasure
      (boundaryProbabilityMeasureTracialState mu) n) := by
    unfold pushedCoordinateTraceMeasure
    infer_instance
  letI : (pushedCoordinateTraceMeasure
      (boundaryProbabilityMeasureTracialState mu) n).Regular := by
    unfold pushedCoordinateTraceMeasure
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro h
  let f := coordinateTestFunction n h
  let a := projectiveComplexCenter (s := antipodalBlockSize n) f
  have hcoordinate :=
    integral_baseCoordinateTraceMeasure_projectiveBlockTraceFunction
      (boundaryProbabilityMeasureTracialState mu) n a
  have hpoint : ∀ z : AntipodalTraceBoundary,
      boundaryTraceFunction (antipodalBaseSummandInclusion n a) z =
        (boundaryCoordinateSet n).indicator (fun w ↦ (h w : Complex)) z := by
    intro z
    exact boundaryTraceFunction_coordinateTestElement n h z
  calc
    ∫ z, h z ∂(pushedCoordinateTraceMeasure
        (boundaryProbabilityMeasureTracialState mu) n) =
        ∫ x, h (boundaryCoordinateEmbedding n x)
          ∂(baseCoordinateTraceMeasure
            (boundaryProbabilityMeasureTracialState mu) n) := by
      rw [pushedCoordinateTraceMeasure]
      change (∫ z, h.toContinuousMap z ∂Measure.map
          (boundaryCoordinateEmbedding n)
          (baseCoordinateTraceMeasure
            (boundaryProbabilityMeasureTracialState mu) n)) =
        ∫ x, h.toContinuousMap (boundaryCoordinateEmbedding n x)
          ∂(baseCoordinateTraceMeasure
            (boundaryProbabilityMeasureTracialState mu) n)
      exact integral_map_of_stronglyMeasurable
        (measurable_boundaryCoordinateEmbedding n)
        h.continuous.stronglyMeasurable
    _ =
      (∫ x, f x
        ∂(baseCoordinateTraceMeasure
          (boundaryProbabilityMeasureTracialState mu) n)).re := by
      change (∫ x, h (boundaryCoordinateEmbedding n x)
          ∂(baseCoordinateTraceMeasure
            (boundaryProbabilityMeasureTracialState mu) n)) =
        (∫ x, ((h (boundaryCoordinateEmbedding n x) : Real) : Complex)
          ∂(baseCoordinateTraceMeasure
            (boundaryProbabilityMeasureTracialState mu) n)).re
      rw [integral_complex_ofReal]
      simp
    _ = (boundaryProbabilityMeasureTracialState mu
        (antipodalBaseSummandInclusion n a)).re :=
      congrArg Complex.re (by
        simpa only [a, projectiveBlockTraceFunction_projectiveComplexCenter]
          using hcoordinate)
    _ = (∫ z, boundaryTraceFunction
        (antipodalBaseSummandInclusion n a) z
          ∂(mu : Measure AntipodalTraceBoundary)).re := rfl
    _ = (∫ z, (boundaryCoordinateSet n).indicator
        (fun w ↦ (h w : Complex)) z
          ∂(mu : Measure AntipodalTraceBoundary)).re := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z
    _ = (∫ z, (h z : Complex)
          ∂((mu : Measure AntipodalTraceBoundary).restrict
            (boundaryCoordinateSet n))).re := by
      rw [integral_indicator (measurableSet_boundaryCoordinateSet n)]
    _ = ∫ z, h z
          ∂((mu : Measure AntipodalTraceBoundary).restrict
            (boundaryCoordinateSet n)) := by
      rw [integral_complex_ofReal]
      simp

end

end STW22AntipodalCoordinateRestriction
end GroupApproximation
