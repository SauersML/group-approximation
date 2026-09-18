import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerGram
import GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.Conjugation
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 2: a unitary dilation of a Hermitian contraction

Let `Yd` be Hermitian with `‖Yd‖ ≤ 1` (L2 operator norm). Diagonalise it as
`Yd = V diag(f) Vᴴ`. Then `|fᵢ| ≤ 1`, because `‖diag f‖ = ‖Vᴴ Yd V‖ ≤ 1`. Put
`D = V diag(√(1 − fᵢ²)) Vᴴ`. This `D` is Hermitian, commutes with `Yd`, and satisfies
`D² = 1 − Yd²`. So `U = Yd + iD` is unitary.

This replaces the Halmos dilation of the manuscript. The Hermitian doubling
`Yd = [[0, y], [yᴴ, 0]]` (part 5) reduces a general contraction `y` to this case.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Square-root defect of a Hermitian contraction.** -/
theorem powersStormer_exists_dilation {Yd : Matrix n n ℂ} (hY : Ydᴴ = Yd) (hn : ‖Yd‖ ≤ 1) :
    ∃ D : Matrix n n ℂ, Dᴴ = D ∧ Yd * D = D * Yd ∧ D * D = 1 - Yd * Yd := by
  obtain ⟨V, f, hV1, hV2, hdiag⟩ := PowersStormer.exists_unitary_diagonalize (d := Yd) hY
  have hYd : Yd = V * diagonal (fun i ↦ (f i : ℂ)) * Vᴴ := by
    rw [← hdiag]
    simp only [← mul_assoc]
    rw [hV1, one_mul, mul_assoc, hV1, mul_one]
  have hdn : ‖diagonal (fun i ↦ (f i : ℂ))‖ ≤ 1 := by
    rw [← hdiag]
    have hVn : ‖V‖ ≤ 1 := powersStormer_norm_le_one_of_conjTranspose_mul_self hV2
    have hVhn : ‖Vᴴ‖ ≤ 1 := by
      rw [l2_opNorm_conjTranspose]
      exact hVn
    calc ‖Vᴴ * Yd * V‖ ≤ ‖Vᴴ * Yd‖ * ‖V‖ := l2_opNorm_mul _ _
      _ ≤ (‖Vᴴ‖ * ‖Yd‖) * ‖V‖ :=
          mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ 1 := mul_le_one₀ (mul_le_one₀ hVhn (norm_nonneg _) hn) (norm_nonneg _) hVn
  rw [l2_opNorm_diagonal] at hdn
  have hf : ∀ i, f i * f i ≤ 1 := fun i ↦ by
    have h1 : ‖((f i : ℝ) : ℂ)‖ ≤ 1 := (norm_le_pi_norm (fun i ↦ (f i : ℂ)) i).trans hdn
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    nlinarith [abs_mul_abs_self (f i), abs_nonneg (f i)]
  have hstar : (star fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ))
      = fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ) := by
    funext i
    simp
  have hdc : diagonal (fun i ↦ (f i : ℂ)) * diagonal (fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ))
      = diagonal (fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ))
        * diagonal (fun i ↦ (f i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hdd : diagonal (fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ))
        * diagonal (fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ))
      = 1 - diagonal (fun i ↦ (f i : ℂ)) * diagonal (fun i ↦ (f i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
      Matrix.diagonal_sub]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr (hf i)), Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul]
  refine ⟨V * diagonal (fun i ↦ ((Real.sqrt (1 - f i * f i) : ℝ) : ℂ)) * Vᴴ, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, ← mul_assoc, hstar]
  · rw [hYd, powersStormer_conj_mul_conj hV2, powersStormer_conj_mul_conj hV2, hdc]
  · rw [powersStormer_conj_mul_conj hV2, hdd, hYd, powersStormer_conj_mul_conj hV2, mul_sub,
      sub_mul, mul_one, hV1]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_exists_dilation

/-- Expansion of `(A + a B)(A + b B)`. -/
theorem powersStormer_add_smul_mul_add_smul (A B : Matrix n n ℂ) (a b : ℂ) :
    (A + a • B) * (A + b • B) = A * A + b • (A * B) + a • (B * A) + (a * b) • (B * B) := by
  rw [add_mul, mul_add, mul_add, mul_smul_comm b A B, smul_mul_assoc a B A,
    smul_mul_assoc a B (b • B), mul_smul_comm b B B, smul_smul, ← add_assoc]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_add_smul_mul_add_smul

/-- **The dilation is unitary.** If `Yd` and `D` are commuting Hermitian matrices with
`D² = 1 − Yd²`, then `U = Yd + iD` satisfies `UᴴU = UUᴴ = 1`. -/
theorem powersStormer_unitary_of_dilation {Yd D : Matrix n n ℂ} (hY : Ydᴴ = Yd) (hD : Dᴴ = D)
    (hc : Yd * D = D * Yd) (hDD : D * D = 1 - Yd * Yd) :
    (Yd + Complex.I • D)ᴴ * (Yd + Complex.I • D) = 1 ∧
      (Yd + Complex.I • D) * (Yd + Complex.I • D)ᴴ = 1 := by
  have hU : (Yd + Complex.I • D)ᴴ = Yd + (-Complex.I) • D := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hY, hD, powersStormer_star_I]
  rw [hU]
  constructor
  · rw [powersStormer_add_smul_mul_add_smul, hc, neg_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, hDD]
    abel
  · rw [powersStormer_add_smul_mul_add_smul, hc, neg_smul, mul_neg, Complex.I_mul_I, neg_neg,
      one_smul, hDD]
    abel

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_unitary_of_dilation

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
