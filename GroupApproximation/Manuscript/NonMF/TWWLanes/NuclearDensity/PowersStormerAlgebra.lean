import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerBlocks
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 5: commutator algebra for the Powers--Størmer assembly

Finite-dimensional identities and estimates over an arbitrary finite index type `n`:

* the commutator of `Yd + iD` with `X` splits as `[Yd, X] + i[D, X]`, which gives
  `‖[Yd, X]‖₂² ≤ ‖[Yd + iD, X]‖₂²` for Hermitian `Yd`, `D` and `X`;
* `re tr([Yd + iD, X] G) ≤ |tr([Yd, X] G)| + |tr(D X G)| + |tr(X D G)|`;
* two Cauchy--Schwarz estimates `|tr(D T² G)|² ≤ tr(T²) tr(D² T²)` for unitary `G`;
* block identities for the Hermitian doubling `[[0, y], [yᴴ, 0]]`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator with `Yd + iD` splits. -/
theorem powersStormer_commutator_add_I_smul (Yd D X : Matrix n n ℂ) :
    (Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)
      = (Yd * X - X * Yd) + Complex.I • (D * X - X * D) := by
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_commutator_add_I_smul

/-- The commutator of two Hermitian matrices is skew-adjoint. -/
theorem powersStormer_commutator_conjTranspose {A B : Matrix n n ℂ} (hA : Aᴴ = A)
    (hB : Bᴴ = B) : (A * B - B * A)ᴴ = -(A * B - B * A) := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hA, hB, neg_sub]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_commutator_conjTranspose

/-- For Hermitian `Yd`, `D` and `X`: `‖[Yd, X]‖₂² ≤ ‖[Yd + iD, X]‖₂²`. -/
theorem powersStormer_re_trace_gram_commutator_le {Yd D X : Matrix n n ℂ} (hY : Ydᴴ = Yd)
    (hD : Dᴴ = D) (hX : Xᴴ = X) :
    (trace ((Yd * X - X * Yd)ᴴ * (Yd * X - X * Yd))).re
      ≤ (trace (((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D))ᴴ
          * ((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)))).re := by
  rw [powersStormer_commutator_add_I_smul Yd D X,
    powersStormer_trace_gram_add_I_smul (powersStormer_commutator_conjTranspose hY hX)
      (powersStormer_commutator_conjTranspose hD hX), Complex.add_re]
  linarith [powersStormer_re_trace_gram_nonneg (D * X - X * D)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_re_trace_gram_commutator_le

/-- `re tr([Yd + iD, X] G) ≤ |tr([Yd, X] G)| + (|tr(D X G)| + |tr(X D G)|)`. -/
theorem powersStormer_re_trace_commutator_mul_le (Yd D X G : Matrix n n ℂ) :
    (trace (((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)) * G)).re
      ≤ ‖trace ((Yd * X - X * Yd) * G)‖
        + (‖trace (D * X * G)‖ + ‖trace (X * D * G)‖) := by
  have e : trace (((Yd + Complex.I • D) * X - X * (Yd + Complex.I • D)) * G)
      = trace ((Yd * X - X * Yd) * G)
        + Complex.I * (trace (D * X * G) - trace (X * D * G)) := by
    rw [powersStormer_commutator_add_I_smul Yd D X, add_mul, trace_add, smul_mul_assoc,
      trace_smul, smul_eq_mul, sub_mul (D * X) (X * D) G, trace_sub]
  rw [e]
  refine (Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith [norm_sub_le (trace (D * X * G)) (trace (X * D * G))]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_re_trace_commutator_mul_le

/-- `tr(Zᴴ X) = conj tr(Z Xᴴ)`. -/
theorem powersStormer_trace_conjTranspose_mul (Z X : Matrix n n ℂ) :
    trace (Zᴴ * X) = star (trace (Z * Xᴴ)) := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, trace_mul_comm]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_trace_conjTranspose_mul

/-- **Two Cauchy--Schwarz estimates.** For Hermitian `T`, `D` and unitary `G`:
`|tr(D T² G)|² ≤ tr(T²) tr(D² T²)` and `|tr(T² D G)|² ≤ tr(D² T²) tr(T²)`. -/
theorem powersStormer_norm_trace_sq_pair {T D G : Matrix n n ℂ} (hT : Tᴴ = T) (hD : Dᴴ = D)
    (hG1 : Gᴴ * G = 1) (hG2 : G * Gᴴ = 1) :
    ‖trace (D * (T * T) * G)‖ ^ 2 ≤ (trace (T * T)).re * (trace (D * D * (T * T))).re ∧
      ‖trace (T * T * D * G)‖ ^ 2 ≤ (trace (D * D * (T * T))).re * (trace (T * T)).re := by
  have e1 : trace (D * (T * T) * G) = trace ((Gᴴ * T)ᴴ * (D * T)) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hT, trace_mul_comm (T * G) (D * T)]
    simp only [mul_assoc]
  have e2 : trace (T * T * D * G) = trace ((D * T)ᴴ * (G * T)) := by
    rw [conjTranspose_mul, hT, hD, trace_mul_comm (T * D) (G * T),
      trace_mul_comm (T * T * D) G]
    simp only [mul_assoc]
  have gA : trace ((Gᴴ * T)ᴴ * (Gᴴ * T)) = trace (T * T) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hT, mul_assoc, ← mul_assoc G Gᴴ T, hG2,
      one_mul]
  have gB : trace ((D * T)ᴴ * (D * T)) = trace (D * D * (T * T)) := by
    rw [conjTranspose_mul, hT, hD]
    simp only [mul_assoc]
    rw [trace_mul_comm T]
    simp only [mul_assoc]
  have gC : trace ((G * T)ᴴ * (G * T)) = trace (T * T) := by
    rw [conjTranspose_mul, hT, mul_assoc, ← mul_assoc Gᴴ G T, hG1, one_mul]
  have hA := powersStormer_norm_trace_sq_le (Gᴴ * T) (D * T)
  have hB := powersStormer_norm_trace_sq_le (D * T) (G * T)
  rw [← e1, gA, gB] at hA
  rw [← e2, gB, gC] at hB
  exact ⟨hA, hB⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_trace_sq_pair

/-- The Hermitian doubling `[[0, y], [yᴴ, 0]]` is Hermitian. -/
theorem powersStormer_doubling_conjTranspose (y : Matrix n n ℂ) :
    (fromBlocks 0 y yᴴ 0)ᴴ = fromBlocks 0 y yᴴ 0 := by
  rw [fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_conjTranspose]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_doubling_conjTranspose

/-- `1 − Yd² = diag(1 − yyᴴ, 1 − yᴴy)` for the Hermitian doubling `Yd`. -/
theorem powersStormer_one_sub_doubling_sq (y : Matrix n n ℂ) :
    1 - fromBlocks 0 y yᴴ 0 * fromBlocks 0 y yᴴ 0
      = fromBlocks (1 - y * yᴴ) 0 0 (1 - yᴴ * y) := by
  rw [fromBlocks_multiply, ← fromBlocks_one, powersStormer_fromBlocks_sub]
  simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_one_sub_doubling_sq

/-- `diag(T, T)² = diag(h, h)` when `T² = h`. -/
theorem powersStormer_diag_mul_diag {T h : Matrix n n ℂ} (hTh : T * T = h) :
    fromBlocks T 0 0 T * fromBlocks T 0 0 T = fromBlocks h 0 0 h := by
  rw [fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, hTh]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_diag_mul_diag

/-- `tr(diag(P, Q) diag(h, h)) = tr(P h) + tr(Q h)`. -/
theorem powersStormer_trace_diag_mul_diag (P Q h : Matrix n n ℂ) :
    trace (fromBlocks P 0 0 Q * fromBlocks h 0 0 h) = trace (P * h) + trace (Q * h) := by
  rw [fromBlocks_multiply, powersStormer_trace_fromBlocks]
  simp only [mul_zero, add_zero, zero_add]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_trace_diag_mul_diag

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
