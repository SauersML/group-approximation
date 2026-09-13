import GroupApproximation.ThompsonOre.ThompsonShift
import GroupApproximation.ThompsonOre.ThompsonOrder
import GroupApproximation.ThompsonOre.ShiftOreBrown
import GroupApproximation.ThompsonOre.X1Answer

/-!
# Guba's Question 3.20 for Thompson's group `F`

Question 3.20 of V. Guba, *Amenability problem for Thompson's group F: state of the art*,
arXiv:2305.07113v4, asks whether, for every `b ∈ K[F]`, the equation `(1 - x1) u = b v` has a
non-zero solution. This file proves it for `ThompsonF`, presentation (1.2) of the survey. It
supplies the inputs that `one_sub_solution_of_nested` needs:
* `K[F]` has no zero divisors (`ThompsonOrder`).
* Theorem 3.18 for `x0`, from the shift argument for Brown's frame (`ShiftOreBrown`), carried to
  `F` along `thompsonEquivBrown`.
* The subgroup `halfFix` of elements fixing `(-∞, 1]` contains `x1`, and `halfFixEquiv` sends
  `x1` to `x0`. Conjugates of `halfFix` are nested (`ThompsonShift`).

`one_sub_x1_solution` states both readings of "non-zero solution": a pair `(u, v) ≠ (0, 0)` for
every `b`, and a nonzero common multiple `b v` for every nonzero `b`.
-/

namespace GroupApproximation.ThompsonOre

open MonoidAlgebra HigmanThompson

/-- Brown's positive frame, moved to `F`, has `x0` as its generator `x 0`. -/
theorem brownFrame_map_x_zero : (brownFrame.map thompsonEquivBrown.symm).x 0 = x0 := by
  show thompsonEquivBrown.symm (brownX 0 0)⁻¹ = x0
  rw [thompsonEquivBrown_symm_apply, map_inv, fromBrown_X, inv_inv, xn_zero]

/-- **Theorem 3.18 of the survey for `F`**: every nonzero `b ∈ K[F]` has a nonzero right multiple
in `(1 - x0) K[F]`. -/
theorem exists_mul_ne_zero_one_sub_x0_mul_eq_mul {K : Type*} [Field K]
    (b : MonoidAlgebra K ThompsonF) (hb : b ≠ 0) :
    ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K ThompsonF x0) * u := by
  have h :=
    (brownFrame.map thompsonEquivBrown.symm).exists_mul_ne_zero_one_sub_x_zero_mul_eq_mul b hb
  rwa [brownFrame_map_x_zero] at h

/-- **Question 3.20 of the survey for `F`.** For every `b ∈ K[F]` the equation
`(1 - x1) u = b v` has a solution with `(u, v) ≠ (0, 0)`. For every nonzero `b` it has a solution
with `b v ≠ 0`, so the right ideals `(1 - x1) K[F]` and `b K[F]` meet in a nonzero element. -/
theorem one_sub_x1_solution {K : Type*} [Field K] (b : MonoidAlgebra K ThompsonF) :
    (∃ u v : MonoidAlgebra K ThompsonF, (u ≠ 0 ∨ v ≠ 0) ∧ (1 - of K ThompsonF x1) * u = b * v) ∧
      (b ≠ 0 → ∃ u v : MonoidAlgebra K ThompsonF, b * v ≠ 0 ∧
        (1 - of K ThompsonF x1) * u = b * v) :=
  one_sub_solution_of_nested x0 x1 halfFix x1_mem_halfFix halfFixEquiv halfFixEquiv_x1
    exists_mul_ne_zero_one_sub_x0_mul_eq_mul halfFix_conj_chain b

end GroupApproximation.ThompsonOre
