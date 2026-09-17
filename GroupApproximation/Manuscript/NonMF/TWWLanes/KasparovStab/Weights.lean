import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Series
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: the Mingo--Phillips weights

* `coef n = 2⁻ⁿ` and `wt n = coef n ^ 2`, the diagonal weights of the operator.
* `gen x n`: the `n`-th rescaled generator. `n` is decoded as `(k, j) = Nat.unpair n`,
  so every generator `x k` occurs infinitely often, at every scale, with
  `‖gen x n‖ ≤ coef n`.
* `summable_of_norm_le_coef`: a sequence dominated by `coef n * K` lies in `H_B`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v w

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The scale `2⁻ⁿ`. -/
noncomputable def coef (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coef

theorem coef_pos (n : ℕ) : 0 < coef n := pow_pos (by norm_num) n

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coef_pos

theorem coef_nonneg (n : ℕ) : 0 ≤ coef n := (coef_pos n).le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coef_nonneg

theorem coef_le_one (n : ℕ) : coef n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coef_le_one

/-- The diagonal weight `4⁻ⁿ`. -/
noncomputable def wt (n : ℕ) : ℝ := coef n * coef n

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.wt

theorem wt_pos (n : ℕ) : 0 < wt n := mul_pos (coef_pos n) (coef_pos n)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.wt_pos

theorem wt_le_coef (n : ℕ) : wt n ≤ coef n :=
  mul_le_of_le_one_left (coef_nonneg n) (coef_le_one n)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.wt_le_coef

/-- The rescaled generator: `2⁻ⁿ (1 + ‖x k‖)⁻¹ x k` with `k = (Nat.unpair n).1`. -/
noncomputable def gen {E : CStarModule.{v, w} B} (x : ℕ → E.carrier) (n : ℕ) : E.carrier :=
  ((coef n * (1 + E.norm (x (Nat.unpair n).1))⁻¹ : ℝ) : ℂ) • x (Nat.unpair n).1

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.gen

theorem norm_gen_le {E : CStarModule.{v, w} B} (x : ℕ → E.carrier) (n : ℕ) :
    E.norm (gen x n) ≤ coef n := by
  have ha := E.norm_nonneg (x (Nat.unpair n).1)
  have hpos : 0 < 1 + E.norm (x (Nat.unpair n).1) := by linarith
  have hinv : 0 ≤ (1 + E.norm (x (Nat.unpair n).1))⁻¹ := inv_nonneg.mpr hpos.le
  have hc : 0 ≤ coef n * (1 + E.norm (x (Nat.unpair n).1))⁻¹ :=
    mul_nonneg (coef_nonneg n) hinv
  rw [gen, E.norm_smul, Complex.norm_of_nonneg hc, mul_assoc]
  calc coef n * ((1 + E.norm (x (Nat.unpair n).1))⁻¹ * E.norm (x (Nat.unpair n).1))
      ≤ coef n * ((1 + E.norm (x (Nat.unpair n).1))⁻¹
          * (1 + E.norm (x (Nat.unpair n).1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith) hinv) (coef_nonneg n)
    _ = coef n := by rw [inv_mul_cancel₀ hpos.ne', mul_one]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.norm_gen_le

/-- **A sequence dominated by `2⁻ⁿ K` lies in `H_B`.** -/
theorem summable_of_norm_le_coef {a : ℕ → B} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ n, ‖a n‖ ≤ coef n * K) : Summable fun n => star (a n) * a n := by
  refine Summable.of_norm_bounded (summable_geometric_two.mul_left (K ^ 2)) fun n => ?_
  calc ‖star (a n) * a n‖ = ‖a n‖ * ‖a n‖ := CStarRing.norm_star_mul_self
    _ ≤ (coef n * K) * (coef n * K) :=
      mul_le_mul (h n) (h n) (norm_nonneg _) (mul_nonneg (coef_nonneg n) hK)
    _ = K ^ 2 * (coef n * coef n) := by ring
    _ ≤ K ^ 2 * coef n := mul_le_mul_of_nonneg_left (wt_le_coef n) (sq_nonneg K)
    _ = K ^ 2 * (1 / 2) ^ n := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.summable_of_norm_le_coef

theorem star_ofReal_complex (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  rw [← starRingEnd_apply, Complex.conj_ofReal]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.star_ofReal_complex

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
