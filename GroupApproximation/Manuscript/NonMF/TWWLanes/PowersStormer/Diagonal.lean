import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import GroupApproximation.Meta.AxiomGuard

/-!
# Powers–Størmer inequality, diagonal core (lane nm-tww-10, part 1)

Target (unnormalised trace-norm form): for positive semidefinite `h k : Matrix n n ℂ`,
`‖h - k‖_HS ^ 2 ≤ ‖h ^ 2 - k ^ 2‖_1`.

Proof route. Everything reduces to the case where `h - k` is diagonal.
* Choose a unitary `U` with `Uᴴ (h - k) U = diag λ` (spectral theorem), and replace
  `h, k` by `Uᴴ h U, Uᴴ k U`. These are still positive semidefinite, and traces do not change.
* Now let `h - k = diag λ` and `s = h + k`. The identity `2 (h h - k k) = (h - k) s + s (h - k)`
  gives `(h h - k k)ᵢᵢ = λᵢ (hᵢᵢ + kᵢᵢ)`.
* Let `σᵢ = ±1` be the sign of `λᵢ` and `S = diag σ`, a self-adjoint unitary. Then
  `re tr((h h - k k) S) = ∑ᵢ |λᵢ| (re hᵢᵢ + re kᵢᵢ)`.
* The diagonal entries of positive semidefinite matrices are nonnegative, and
  `λᵢ = re hᵢᵢ - re kᵢᵢ`. So `|λᵢ| ≤ re hᵢᵢ + re kᵢᵢ` and `λᵢ ^ 2 ≤ |λᵢ| (re hᵢᵢ + re kᵢᵢ)`.
  Summing gives `re tr((h - k)(h - k)) ≤ re tr((h h - k k) S)`.
* Finally `|tr(x u)| ≤ ‖x‖_1` for every unitary `u` (file `Norms.lean`).

This proof does not use spectral projections or products of positive matrices: once
`h - k` is diagonalised, the whole estimate is entrywise.

This file proves the diagonal step `re_trace_sq_le_of_sub_eq_diagonal`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace PowersStormer

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*}

/-- The sign pattern of a real vector: `1` where the entry is nonnegative, `-1` elsewhere. -/
def signPattern (f : n → ℝ) (i : n) : ℝ :=
  if 0 ≤ f i then 1 else -1

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.signPattern

theorem signPattern_mul_self (f : n → ℝ) (i : n) :
    signPattern f i * signPattern f i = 1 := by
  by_cases hpos : 0 ≤ f i
  · rw [signPattern, if_pos hpos]
    norm_num
  · rw [signPattern, if_neg hpos]
    norm_num

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.signPattern_mul_self

/-- The scalar estimate: if `a b ≥ 0` and `a - b = t`, then `t ^ 2 ≤ t σ(t) (a + b)`. -/
theorem sq_le_mul_signPattern_mul_add (f : n → ℝ) (i : n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a - b = f i) :
    f i * f i ≤ f i * signPattern f i * (a + b) := by
  have e : f i * (a - b) = f i * f i := by rw [hab]
  by_cases hpos : 0 ≤ f i
  · rw [signPattern, if_pos hpos]
    nlinarith [mul_nonneg hpos hb, e]
  · rw [signPattern, if_neg hpos]
    have hneg : f i < 0 := not_le.mp hpos
    nlinarith [mul_nonneg (neg_nonneg.mpr hneg.le) ha, e]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.sq_le_mul_signPattern_mul_add

variable [Fintype n] [DecidableEq n]

/-- If `h - k` is diagonal with real entries `f`, then the diagonal entries of `h h - k k` are
`f i (h i i + k i i)`. The reason is `2 (h h - k k) = (h - k)(h + k) + (h + k)(h - k)`. -/
theorem sq_sub_sq_diag_of_sub_eq_diagonal {h k : Matrix n n ℂ} {f : n → ℝ}
    (hd : h - k = diagonal (fun i => (f i : ℂ))) (i : n) :
    (h * h - k * k) i i = (f i : ℂ) * (h i i + k i i) := by
  have hid : h * h - k * k + (h * h - k * k) = (h - k) * (h + k) + (h + k) * (h - k) := by
    noncomm_ring
  rw [hd] at hid
  have hii := congrArg (fun M : Matrix n n ℂ => M i i) hid
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal] at hii
  rw [Matrix.sub_apply]
  linear_combination hii / 2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.sq_sub_sq_diag_of_sub_eq_diagonal

/-- The real part of `tr((h - k)(h - k))` when `h - k = diag f`. -/
theorem re_trace_sub_mul_sub_of_sub_eq_diagonal {h k : Matrix n n ℂ} {f : n → ℝ}
    (hd : h - k = diagonal (fun i => (f i : ℂ))) :
    (trace ((h - k) * (h - k))).re = ∑ i, f i * f i := by
  simp only [hd, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.re_trace_sub_mul_sub_of_sub_eq_diagonal

/-- The real part of `tr((h h - k k) diag σ)` when `h - k = diag f` and `σ` is the sign
pattern of `f`. -/
theorem re_trace_sq_sub_sq_mul_sign_of_sub_eq_diagonal {h k : Matrix n n ℂ} {f : n → ℝ}
    (hd : h - k = diagonal (fun i => (f i : ℂ))) :
    (trace ((h * h - k * k) * diagonal (fun i => (signPattern f i : ℂ)))).re =
      ∑ i, f i * signPattern f i * ((h i i).re + (k i i).re) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq_sub_sq_diag_of_sub_eq_diagonal hd i]
  have hcast : (f i : ℂ) * (h i i + k i i) * (signPattern f i : ℂ) =
      ((f i * signPattern f i : ℝ) : ℂ) * (h i i + k i i) := by
    push_cast
    ring
  rw [hcast, Complex.re_ofReal_mul, Complex.add_re]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.re_trace_sq_sub_sq_mul_sign_of_sub_eq_diagonal

/-- **Diagonal Powers–Størmer core.** Let `h, k` be positive semidefinite with `h - k = diag f`.
Then `re tr((h - k)(h - k)) ≤ re tr((h h - k k) S)`, where `S = diag(sign f)`. -/
theorem re_trace_sq_le_of_sub_eq_diagonal {h k : Matrix n n ℂ} (hh : h.PosSemidef)
    (hk : k.PosSemidef) {f : n → ℝ} (hd : h - k = diagonal (fun i => (f i : ℂ))) :
    (trace ((h - k) * (h - k))).re ≤
      (trace ((h * h - k * k) * diagonal (fun i => (signPattern f i : ℂ)))).re := by
  rw [re_trace_sub_mul_sub_of_sub_eq_diagonal hd,
    re_trace_sq_sub_sq_mul_sign_of_sub_eq_diagonal hd]
  refine Finset.sum_le_sum fun i _ => ?_
  have ha : 0 ≤ (h i i).re := (Complex.nonneg_iff.mp (hh.diag_nonneg (i := i))).1
  have hb : 0 ≤ (k i i).re := (Complex.nonneg_iff.mp (hk.diag_nonneg (i := i))).1
  have hab : (h i i).re - (k i i).re = f i := by
    have hii := congrArg (fun M : Matrix n n ℂ => (M i i).re) hd
    simp only [Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] at hii
    exact hii
  exact sq_le_mul_signPattern_mul_add f i ha hb hab

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.re_trace_sq_le_of_sub_eq_diagonal

end

end PowersStormer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
