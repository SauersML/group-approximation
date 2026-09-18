import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.DiagonalMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 1: Hilbert--Schmidt algebra for the Powers--Størmer route

This part holds finite-dimensional helpers over an arbitrary finite index type `n`, with the
L2 operator norm.

* `powersStormer_norm_trace_sq_le`: Cauchy--Schwarz, `|tr(Aᴴ B)|² ≤ tr(AᴴA) tr(BᴴB)`.
* `powersStormer_trace_gram_add_I_smul`: if `K` and `L` are skew-adjoint, then
  `tr((K + iL)ᴴ(K + iL)) = tr(KᴴK) + tr(LᴴL)`.
* `powersStormer_norm_le_one_of_conjTranspose_mul_self`: an isometry has operator norm
  at most `1`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Hilbert--Schmidt norm is nonnegative (any finite index type). -/
theorem powersStormer_re_trace_gram_nonneg (Z : Matrix n n ℂ) :
    0 ≤ (trace (Zᴴ * Z)).re := by
  rw [ConnesTrick.re_trace_conjTranspose_mul_self]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_re_trace_gram_nonneg

/-- **Cauchy--Schwarz for the Hilbert--Schmidt pairing.** -/
theorem powersStormer_norm_trace_sq_le (A B : Matrix n n ℂ) :
    ‖trace (Aᴴ * B)‖ ^ 2 ≤ (trace (Aᴴ * A)).re * (trace (Bᴴ * B)).re := by
  have hsum : trace (Aᴴ * B) = ∑ i, ∑ j, star (A j i) * B j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsum, ConnesTrick.re_trace_conjTranspose_mul_self A,
    ConnesTrick.re_trace_conjTranspose_mul_self B]
  calc ‖∑ i, ∑ j, star (A j i) * B j i‖ ^ 2
      ≤ (∑ i, ∑ j, ‖A j i‖ * ‖B j i‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        exact le_of_eq (by rw [norm_mul, norm_star])
    _ = (∑ p : n × n, ‖A p.2 p.1‖ * ‖B p.2 p.1‖) ^ 2 := by
        simp only [Fintype.sum_prod_type]
    _ ≤ (∑ p : n × n, ‖A p.2 p.1‖ ^ 2) * ∑ p : n × n, ‖B p.2 p.1‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * ∑ i, ∑ j, Complex.normSq (B i j) := by
        simp only [Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]
        congr 1 <;> exact Finset.sum_comm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_trace_sq_le

/-- `star i = -i` in `ℂ`. -/
theorem powersStormer_star_I : (star Complex.I : ℂ) = -Complex.I :=
  Complex.conj_I

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_star_I

/-- For skew-adjoint `K` and `L`, the Hilbert--Schmidt norm of `K + iL` splits:
`tr((K + iL)ᴴ(K + iL)) = tr(KᴴK) + tr(LᴴL)`. -/
theorem powersStormer_trace_gram_add_I_smul {K L : Matrix n n ℂ} (hK : Kᴴ = -K)
    (hL : Lᴴ = -L) :
    trace ((K + Complex.I • L)ᴴ * (K + Complex.I • L)) = trace (Kᴴ * K) + trace (Lᴴ * L) := by
  have e1 : (K + Complex.I • L)ᴴ * (K + Complex.I • L)
      = Kᴴ * K + Complex.I • (Kᴴ * L) + star Complex.I • (Lᴴ * K)
        + (star Complex.I * Complex.I) • (Lᴴ * L) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, add_mul, mul_add, mul_add,
      smul_mul_assoc (star Complex.I) Lᴴ K, smul_mul_assoc (star Complex.I) Lᴴ (Complex.I • L),
      mul_smul_comm Complex.I Kᴴ L, mul_smul_comm Complex.I Lᴴ L, smul_smul, ← add_assoc]
  have h3 : trace (Kᴴ * L) = trace (Lᴴ * K) := by
    rw [hK, hL, neg_mul, neg_mul, Matrix.trace_neg, Matrix.trace_neg,
      Matrix.trace_mul_comm L K]
  rw [e1, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, h3,
    powersStormer_star_I]
  linear_combination (-trace (Lᴴ * L)) * Complex.I_mul_I

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_trace_gram_add_I_smul

/-- The identity matrix has operator norm at most `1`. -/
theorem powersStormer_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ ↦ le_of_eq norm_one

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_one_le

/-- An isometry `VᴴV = 1` has operator norm at most `1`. -/
theorem powersStormer_norm_le_one_of_conjTranspose_mul_self {V : Matrix n n ℂ}
    (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self V
  rw [hV] at h
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := powersStormer_norm_one_le
  nlinarith [norm_nonneg V]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_le_one_of_conjTranspose_mul_self

/-- Conjugation `X ↦ V X Vᴴ` by an isometry is multiplicative. -/
theorem powersStormer_conj_mul_conj {V : Matrix n n ℂ} (hV : Vᴴ * V = 1) (A B : Matrix n n ℂ) :
    V * A * Vᴴ * (V * B * Vᴴ) = V * (A * B) * Vᴴ := by
  simp only [mul_assoc]
  rw [← mul_assoc Vᴴ V, hV, one_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_conj_mul_conj

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
