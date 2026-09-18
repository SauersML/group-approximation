import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.Statement
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.Average
import GroupApproximation.Meta.AxiomGuard

/-!
# `PointEvaluationAverageStatement` holds (lane `nm-tww-32`)

`Statement.lean` records the interface of lane `nm-tww-01` as the proposition
`PointEvaluationAverageStatement`: a positive unital continuous functional `τ` on
`C(X, ℂ)`, for compact Hausdorff `X`, agrees on every finite set up to `ε` with an average
`N⁻¹ ∑ᵢ f(xᵢ)` of point evaluations.

Lane `nm-tww-01` is on disk under a different name:
`CommutativeAverage.exists_pointEvaluation_average` (`CommutativeAverage/Average.lean`).
It proves the statement with `N > 0`, from a partition of unity subordinate to a finite
variation cover (`CStarContinuousMapFiniteInterpolation.exists_variation_partition`) and
floor rounding of the weights `τ(wⱼ)` (`CommutativeAverage/Rational.lean`). No
Riesz–Markov step and no literature input.

The only difference is the positivity hypothesis. Here it reads `0 ≤ τ f` in the
`ComplexOrder`, and there it reads `0 ≤ (τ f).re ∧ (τ f).im = 0`. `Complex.nonneg_iff`
converts one into the other.

## Endpoints

* `pointEval_exists_pos_average`: the strengthened form with `0 < N`, in the
  `ComplexOrder` hypothesis shape.
* `pointEvaluationAverageStatement_holds : PointEvaluationAverageStatement.{u}`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeQD

open scoped ComplexOrder

universe u

/-- **Point-evaluation averages, with `N > 0`.** A positive unital continuous functional
on `C(X, ℂ)`, for compact Hausdorff `X`, agrees on every finite set up to `ε` with a
nonempty average of point evaluations. This is lane `nm-tww-01`
(`CommutativeAverage.exists_pointEvaluation_average`) with the positivity hypothesis
restated in the `ComplexOrder`. -/
theorem pointEval_exists_pos_average (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (τ : C(X, ℂ) →L[ℂ] ℂ) (hpos : ∀ f : C(X, ℂ), 0 ≤ f → 0 ≤ τ f)
    (hunit : τ 1 = 1) (F : Finset C(X, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (_ : 0 < N) (x : Fin N → X), ∀ f ∈ F,
      ‖τ f - (N : ℂ)⁻¹ * ∑ i, f (x i)‖ ≤ ε :=
  GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.exists_pointEvaluation_average
    X τ
    (fun f hf => ⟨(Complex.nonneg_iff.1 (hpos f hf)).1,
      (Complex.nonneg_iff.1 (hpos f hf)).2.symm⟩)
    hunit F ε hε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEval_exists_pos_average

/-- **The interface of lane `nm-tww-01` holds unconditionally.** -/
theorem pointEvaluationAverageStatement_holds : PointEvaluationAverageStatement.{u} := by
  unfold PointEvaluationAverageStatement
  intro X _ _ _ τ hpos hunit F ε hε
  obtain ⟨N, _, x, hx⟩ := pointEval_exists_pos_average X τ hpos hunit F ε hε
  exact ⟨N, x, hx⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.pointEvaluationAverageStatement_holds

end CommutativeQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
