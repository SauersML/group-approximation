import GroupApproximation.Analysis.ShulmanHalmosDilationBase

/-! Positivity of the two Halmos defect arguments. -/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

theorem mul_star_self_nonneg (x : A) : 0 ≤ x * star x := by
  simpa only [star_star] using star_mul_self_nonneg (star x)

theorem left_defect_argument_nonneg {x : A} (hx : ‖x‖ ≤ 1) :
    0 ≤ 1 - x * star x := by
  rw [sub_nonneg]
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg x)).mp
  calc
    ‖x * star x‖ = ‖star x‖ * ‖star x‖ := by
      simpa only [star_star] using CStarRing.norm_star_mul_self (x := star x)
    _ = ‖x‖ * ‖x‖ := by rw [norm_star]
    _ ≤ 1 * 1 := mul_le_mul hx hx (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem right_defect_argument_nonneg {x : A} (hx : ‖x‖ ≤ 1) :
    0 ≤ 1 - star x * x := by
  rw [sub_nonneg]
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg x)).mp
  calc
    ‖star x * x‖ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self
    _ ≤ 1 * 1 := mul_le_mul hx hx (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end

end ShulmanHalmosDilation
end GroupApproximation
