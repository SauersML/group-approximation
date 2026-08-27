import GroupApproximation.Analysis.BlackadarKirchbergFiniteDirectSumLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Convex combinations of completely positive maps

The repository already proves closure of complete positivity under addition.
This file supplies the companion needed for finite-dimensional conditional
expectations: multiplication of a completely positive map by a nonnegative
real scalar is completely positive.  The proof stays in the repository's
factorization definition and rescales the matrix square factor by `sqrt t`.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v

noncomputable section

/-- A nonnegative real multiple of a completely positive complex-linear map
is completely positive. -/
theorem IsCompletelyPositive.nonnegativeReal_smul
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {phi : A →ₗ[ℂ] B} (hphi : IsCompletelyPositive phi)
    (t : ℝ) (ht : 0 ≤ t) :
    IsCompletelyPositive ((t : ℂ) • phi) := by
  intro n M hM
  obtain ⟨P, hP⟩ := hphi n M hM
  let c : ℂ := (Real.sqrt t : ℝ)
  have hcstar : star c = c := by simp [c]
  have hcsq : star c * c = (t : ℂ) := by
    rw [hcstar]
    change ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) = (t : ℂ)
    norm_cast
    exact Real.mul_self_sqrt ht
  let Q : CStarMatrix (Fin n) (Fin n) B := fun i j ↦ c • P i j
  refine ⟨Q, ?_⟩
  ext i j
  calc
    (M.map ⇑((t : ℂ) • phi)) i j =
        (t : ℂ) • (M.map ⇑phi) i j := rfl
    _ = (star c * c) • (star P * P) i j := by rw [hcsq, hP]
    _ = ∑ r : Fin n, (star c * c) • (star (P r i) * P r j) := by
      rw [cstarMatrix_mul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by rw [cstarMatrix_star_apply]
    _ = ∑ r : Fin n, star (Q r i) * Q r j := by
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      change (star c * c) • (star (P r i) * P r j) =
        star (c • P r i) * (c • P r j)
      rw [star_smul, smul_mul_smul]
    _ = (star Q * Q) i j := by
      rw [cstarMatrix_mul_apply]
      exact (Finset.sum_congr rfl fun r _ ↦ by rw [cstarMatrix_star_apply]).symm

end

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

#audit_axioms IsCompletelyPositive.nonnegativeReal_smul
