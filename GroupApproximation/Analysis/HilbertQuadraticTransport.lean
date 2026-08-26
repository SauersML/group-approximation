import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Quadratic transport under a contraction

This module records the Hilbert-space-free numerical estimate used when a
vector state is moved by a unitary.  A contraction sends two vectors at
distance at most `epsilon` to vectors at the same distance scale.  Squaring
the triangle inequality gives the corresponding quadratic estimate.

The result is stated for arbitrary complex normed spaces because no inner
product identity is needed at this stage.
-/

namespace GroupApproximation

namespace HilbertQuadraticTransport

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A contraction transports squared norms with the exact quadratic error
obtained by squaring the triangle inequality. -/
theorem norm_apply_sq_le_of_norm_le_one_of_norm_sub_le
    (T : E →L[ℂ] F) (x y : E) (epsilon : ℝ)
    (hT : ‖T‖ ≤ 1) (hxy : ‖y - x‖ ≤ epsilon) :
    ‖T y‖ ^ 2 ≤ ‖T x‖ ^ 2 + 2 * epsilon * ‖T x‖ + epsilon ^ 2 := by
  have hdiff : ‖T (y - x)‖ ≤ epsilon := by
    calc
      ‖T (y - x)‖ ≤ ‖T‖ * ‖y - x‖ := T.le_opNorm (y - x)
      _ ≤ 1 * epsilon :=
        mul_le_mul hT hxy (norm_nonneg _) (by norm_num)
      _ = epsilon := one_mul epsilon
  have hdecomp : T y = T x + T (y - x) := by
    rw [map_sub]
    abel
  have hnorm : ‖T y‖ ≤ ‖T x‖ + epsilon := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hdiff)
  nlinarith [norm_nonneg (T y), norm_nonneg (T x)]

/-- The same estimate with the two vectors interchanged. -/
theorem norm_apply_sq_le_of_norm_le_one_of_norm_sub_le_rev
    (T : E →L[ℂ] F) (x y : E) (epsilon : ℝ)
    (hT : ‖T‖ ≤ 1) (hxy : ‖y - x‖ ≤ epsilon) :
    ‖T x‖ ^ 2 ≤ ‖T y‖ ^ 2 + 2 * epsilon * ‖T y‖ + epsilon ^ 2 := by
  apply norm_apply_sq_le_of_norm_le_one_of_norm_sub_le T y x epsilon hT
  simpa [norm_sub_rev] using hxy

/-- Absolute form of quadratic transport, with the right-hand side measured
at the source vector. -/
theorem abs_norm_apply_sq_sub_le_of_norm_le_one_of_norm_sub_le
    (T : E →L[ℂ] F) (x y : E) (epsilon : ℝ)
    (hT : ‖T‖ ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hxy : ‖y - x‖ ≤ epsilon) :
    |‖T y‖ ^ 2 - ‖T x‖ ^ 2| ≤
      2 * epsilon * ‖T x‖ + epsilon ^ 2 := by
  have hdiffApply : ‖T (y - x)‖ ≤ epsilon := by
    calc
      ‖T (y - x)‖ ≤ ‖T‖ * ‖y - x‖ := T.le_opNorm (y - x)
      _ ≤ 1 * epsilon :=
        mul_le_mul hT hxy (norm_nonneg _) (by norm_num)
      _ = epsilon := one_mul epsilon
  have hnormDiff : |‖T y‖ - ‖T x‖| ≤ epsilon := by
    calc
      |‖T y‖ - ‖T x‖| ≤ ‖T y - T x‖ := abs_norm_sub_norm_le _ _
      _ = ‖T (y - x)‖ := by rw [map_sub]
      _ ≤ epsilon := hdiffApply
  rw [abs_le] at hnormDiff ⊢
  rcases le_total ‖T y‖ ‖T x‖ with hyx | hxyNorm
  · constructor <;>
      nlinarith [hepsilon, norm_nonneg (T x), norm_nonneg (T y)]
  · constructor <;>
      nlinarith [hepsilon, norm_nonneg (T x), norm_nonneg (T y)]

end HilbertQuadraticTransport

end GroupApproximation
