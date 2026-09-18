import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Complex.Order
import GroupApproximation.Meta.AxiomGuard

/-!
# Interface of lane `nm-tww-01`: states on `C(X)` are limits of point-evaluation averages

Lane `nm-tww-02` proves: *every tracial state on a separable unital commutative
C⋆-algebra is quasidiagonal.* The analytic input is lane `nm-tww-01`, which is written in
parallel and not yet on disk (`exists_pointEvaluationAverage` does not occur in the
repository). Following the author brief, its interface is recorded here as a proposition
and asserted nowhere.

## The statement

Let `X` be compact Hausdorff and `τ : C(X, ℂ) → ℂ` a positive unital continuous linear
functional. For every finite `F ⊆ C(X, ℂ)` and `ε > 0` there are points `x₁, …, x_N` with
`‖τ f − N⁻¹ ∑ᵢ f(xᵢ)‖ ≤ ε` for all `f ∈ F`.

## Truth check

`X` is nonempty, because otherwise `C(X, ℂ) = 0` and `τ 1 = 0 ≠ 1`. Every `f ∈ F` is
uniformly continuous, so `X` has a finite open cover `U₁, …, U_m` on each member of which
every `f ∈ F` varies by less than `ε/3`. Take a subordinate partition of unity `hⱼ` and
points `yⱼ ∈ Uⱼ`. Then `‖f − ∑ⱼ f(yⱼ) hⱼ‖∞ ≤ ε/3`, and by positivity `‖τ‖ = τ 1 = 1`, so
`τ f` is within `ε/3` of `∑ⱼ tⱼ f(yⱼ)`. Here `tⱼ = τ hⱼ ≥ 0` and `∑ⱼ tⱼ = 1`. Choose
rationals `kⱼ/N` with `kⱼ ∈ ℕ`, `∑ kⱼ = N` and `∑ⱼ |tⱼ − kⱼ/N| · ‖f‖∞ ≤ ε/3` for all
`f ∈ F`. Then list each `yⱼ` exactly `kⱼ` times. This is the classical density of the
convex hull of point masses in the state space of `C(X)`. The statement is true, and it is
exactly the lane `nm-tww-01` target.

Two simplifications keep it at most as strong as the upstream target. `τ` is required to
be continuous, although positivity alone implies this, and `N = 0` is not excluded.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeQD

open scoped ComplexOrder

universe u

/-- **Interface of lane `nm-tww-01`.** A positive unital continuous functional on
`C(X, ℂ)`, for compact Hausdorff `X`, agrees on every finite set up to `ε` with an
average of point evaluations. It is recorded as a proposition and asserted nowhere. See the
module docstring for the truth check. -/
def PointEvaluationAverageStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (τ : C(X, ℂ) →L[ℂ] ℂ),
    (∀ f : C(X, ℂ), 0 ≤ f → 0 ≤ τ f) → τ 1 = 1 →
    ∀ (F : Finset C(X, ℂ)) (ε : ℝ), 0 < ε →
      ∃ (N : ℕ) (x : Fin N → X),
        ∀ f ∈ F, ‖τ f - (N : ℂ)⁻¹ * ∑ i, f (x i)‖ ≤ ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeQD.PointEvaluationAverageStatement

end CommutativeQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
