import GroupApproximation.Meta.AxiomGuard
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Convex support criterion for the Blackadar--Kirchberg localization step

The finite-coordinate part of the Blackadar--Kirchberg converse is a
finite-dimensional convex-density statement.  This module isolates its
functional-analytic core: a point belongs to the closed convex hull of a set
as soon as every continuous linear functional is no larger at that point
than at some member of the set.  Consequently the point can be approximated,
in norm, by an honest finite convex combination of members of the set.

The formulation is over a complex normed space and tests real parts of
complex continuous linear functionals, matching the Choi-functional support
inequality used for matrix-valued UCP maps.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open Set

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [LocallyConvexSpace ℝ E]

/-- A real-part support inequality against every complex continuous linear
functional puts a point in the closed real convex hull. -/
theorem mem_closedConvexHull_of_complex_support
    (s : Set E) (x : E)
    (hsupport : ∀ f : E →L[ℂ] ℂ, ∃ y ∈ s, (f x).re ≤ (f y).re) :
    x ∈ closedConvexHull ℝ s := by
  by_contra hx
  obtain ⟨f, u, hset, hpoint⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (convex_closedConvexHull (𝕜 := ℝ) (s := s))
      (isClosed_closedConvexHull (𝕜 := ℝ) (s := s)) hx
  obtain ⟨y, hy, hxy⟩ := hsupport f
  have hyHull : y ∈ closedConvexHull ℝ s := subset_closedConvexHull hy
  have hyu : (f y).re < u := hset y hyHull
  exact lt_asymm (hxy.trans_lt hyu) hpoint

/-- Quantitative form of the support criterion: every positive tolerance
contains a finite convex combination of `s` within that tolerance of `x`. -/
theorem exists_convexHull_near_of_complex_support
    (s : Set E) (x : E)
    (hsupport : ∀ f : E →L[ℂ] ℂ, ∃ y ∈ s, (f x).re ≤ (f y).re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ y ∈ convexHull ℝ s, ‖y - x‖ < epsilon := by
  have hxClosed : x ∈ closedConvexHull ℝ s :=
    mem_closedConvexHull_of_complex_support s x hsupport
  have hxClosure : x ∈ closure (convexHull ℝ s) := by
    rwa [← closedConvexHull_eq_closure_convexHull (𝕜 := ℝ)]
  obtain ⟨y, hy, hdist⟩ :=
    Metric.mem_closure_iff.mp hxClosure epsilon hepsilon
  refine ⟨y, hy, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hdist

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms mem_closedConvexHull_of_complex_support
#audit_axioms exists_convexHull_near_of_complex_support
