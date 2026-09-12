import GroupApproximation.Computability.EffectiveMatrixCodePrimrec

/-!
# Effective strict operator-norm certificates

This module turns the power/Frobenius certificates from
`Analysis.OperatorNormCertificate` into executable predicates on the
Gaussian-rational matrix codes of `EffectiveMatrixCode`.

No norm is computed.  A natural number selects a power of the Gram matrix;
the checker then performs only primitive-recursive rational arithmetic and a
strict cross-multiplied comparison.
-/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec
open OperatorNormCertificate
open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Executable powers -/

/-- Power in the unnormalised rational-code field. -/
def ratPow (q : RatCode) : ℕ → RatCode
  | 0 => ratOne
  | n + 1 => ratMul (ratPow q n) q

@[simp] theorem ratPow_zero (q : RatCode) : ratPow q 0 = ratOne := rfl

@[simp] theorem ratPow_succ (q : RatCode) (n : ℕ) :
    ratPow q (n + 1) = ratMul (ratPow q n) q := rfl

@[simp] theorem toRat_ratPow (q : RatCode) (n : ℕ) :
    toRat (ratPow q n) = toRat q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ratPow, ih, pow_succ]

/-- Matrix power in the fixed natural nonempty dimension `d + 1`. -/
def matrixPow (d : ℕ) (A : MatrixCode) : ℕ → MatrixCode
  | 0 => identity d
  | n + 1 => matrixMul d (matrixPow d A n) A

@[simp] theorem matrixPow_zero (d : ℕ) (A : MatrixCode) :
    matrixPow d A 0 = identity d := rfl

@[simp] theorem matrixPow_succ (d : ℕ) (A : MatrixCode) (n : ℕ) :
    matrixPow d A (n + 1) = matrixMul d (matrixPow d A n) A := rfl

@[simp] theorem toMatrix_matrixPow (d : ℕ) (A : MatrixCode) (n : ℕ) :
    toMatrix d (matrixPow d A n) = (toMatrix d A) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [matrixPow, ih, pow_succ]

/-! ## A rational code for the Frobenius quantity -/

/-- Sum of squared moduli in row `i`. -/
def froRowSqCode (d : ℕ) (A : MatrixCode) (i : ℕ) : RatCode :=
  (List.range (dim d)).foldl
    (fun q j => ratAdd q (complexNormSq (entry d A i j))) ratZero

/-- Sum of squared moduli of every entry. -/
def froSqCode (d : ℕ) (A : MatrixCode) : RatCode :=
  (List.range (dim d)).foldl
    (fun q i => ratAdd q (froRowSqCode d A i)) ratZero

private theorem ratFoldRange_semantics (n : ℕ) (f : ℕ → RatCode) :
    toRat ((List.range n).foldl (fun q i => ratAdd q (f i)) ratZero) =
      ∑ i : Fin n, toRat (f i) := by
  have hfold :
      toRat ((List.range n).foldl (fun q i => ratAdd q (f i)) ratZero) =
        ((List.range n).map fun i => toRat (f i)).sum := by
    rw [← List.foldl_map]
    simpa only [toRat_zero, zero_add, List.map_map, Function.comp_def] using
      (EffectiveMatrixCode.toRat_foldl ratZero
        ((List.range n).map fun i => f i))
  rw [hfold, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range, Finset.sum_range]

theorem toRat_froRowSqCode (d : ℕ) (A : MatrixCode) (i : Fin (dim d)) :
    (toRat (froRowSqCode d A i) : ℝ) =
      ∑ j : Fin (dim d), ‖toMatrix d A i j‖ ^ 2 := by
  rw [froRowSqCode, ratFoldRange_semantics]
  push_cast
  simp only [toRat_complexNormSq, toMatrix]

/-- The Frobenius code represents exactly the analytic Frobenius quantity. -/
@[simp] theorem toRat_froSqCode (d : ℕ) (A : MatrixCode) :
    (toRat (froSqCode d A) : ℝ) =
      OperatorNormCertificate.froSq (toMatrix d A) := by
  rw [froSqCode, ratFoldRange_semantics]
  push_cast
  simp only [toRat_froRowSqCode]
  rfl

/-! ## Gram powers and threshold codes -/

/-- The `2^m`-th power of `Aᴴ A`. -/
def gramPowCode (d : ℕ) (A : MatrixCode) (m : ℕ) : MatrixCode :=
  matrixPow d (matrixMul d (conjTranspose d A) A) (2 ^ m)

@[simp] theorem toMatrix_gramPowCode (d : ℕ) (A : MatrixCode) (m : ℕ) :
    toMatrix d (gramPowCode d A m) =
      ((toMatrix d A)ᴴ * toMatrix d A) ^ 2 ^ m := by
  simp [gramPowCode]

/-- Code for `1 / (k + 1)`. -/
def ratInvSucc (k : ℕ) : RatCode := ((1, 0), k)

@[simp] theorem toRat_ratInvSucc (k : ℕ) :
    toRat (ratInvSucc k) = 1 / (k + 1 : ℚ) := by
  simp [ratInvSucc, toRat, numeratorPos, numeratorNeg, denominator]

/-! ## Logical certificate predicates -/

/-- A natural witness that `‖A‖ < 1 / (k + 1)`. -/
def upperNormCert (d k : ℕ) (A : MatrixCode) (m : ℕ) : Prop :=
  RatLt
    (ratMul (ratOfNat ((dim d) ^ 4))
      (froSqCode d (gramPowCode d A m)))
    (ratPow (ratInvSucc k) (2 ^ (m + 2)))

instance upperNormCertDecidable (d k : ℕ) (A : MatrixCode) (m : ℕ) :
    Decidable (upperNormCert d k A m) := by
  unfold upperNormCert
  infer_instance

/-- A natural witness that `1 / 3 < ‖A‖`. -/
def lowerThirdCert (d : ℕ) (A : MatrixCode) (m : ℕ) : Prop :=
  RatLt
    (ratMul (ratOfNat ((dim d) ^ 2))
      (ratPow (ratInvSucc 2) (2 ^ (m + 2))))
    (froSqCode d (gramPowCode d A m))

instance lowerThirdCertDecidable (d : ℕ) (A : MatrixCode) (m : ℕ) :
    Decidable (lowerThirdCert d A m) := by
  unfold lowerThirdCert
  infer_instance

/-- Soundness of the executable strict upper certificate. -/
theorem opNorm_lt_invSucc_of_upperNormCert (d k : ℕ) (A : MatrixCode)
    (m : ℕ) (h : upperNormCert d k A m) :
    ‖toMatrix d A‖ < 1 / ((k : ℝ) + 1) := by
  apply OperatorNormCertificate.opNorm_lt_of_certificate
    (toMatrix d A) (show 0 < 1 / ((k : ℝ) + 1) by positivity) m
  have hq := (ratLt_iff _ _).1 h
  have hr :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 4))
        (froSqCode d (gramPowCode d A m))) : ℚ) : ℝ) <
        ((toRat (ratPow (ratInvSucc k) (2 ^ (m + 2))) : ℚ) : ℝ)) := by
    exact_mod_cast hq
  norm_num [toRat_mul, toRat_ratOfNat, toRat_froSqCode,
    toMatrix_gramPowCode, toRat_ratPow, toRat_ratInvSucc,
    Fintype.card_fin] at hr ⊢
  simpa only [Nat.cast_pow] using hr

/-- Completeness of the executable strict upper certificate. -/
theorem exists_upperNormCert_of_opNorm_lt_invSucc (d k : ℕ)
    (A : MatrixCode) (h : ‖toMatrix d A‖ < 1 / ((k : ℝ) + 1)) :
    ∃ m, upperNormCert d k A m := by
  obtain ⟨m, hm⟩ := OperatorNormCertificate.exists_certificate_of_opNorm_lt
    (toMatrix d A) (show 0 < 1 / ((k : ℝ) + 1) by positivity) h
  refine ⟨m, ?_⟩
  apply (ratLt_iff _ _).2
  have hr :
      ((((Fintype.card (Fin (dim d)) : ℕ) : ℝ) ^ 4 *
        OperatorNormCertificate.froSq
          (((toMatrix d A)ᴴ * toMatrix d A) ^ 2 ^ m)) <
        (1 / ((k : ℝ) + 1)) ^ 2 ^ (m + 2)) := hm
  have hrat :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 4))
        (froSqCode d (gramPowCode d A m))) : ℚ) : ℝ) <
        ((toRat (ratPow (ratInvSucc k) (2 ^ (m + 2))) : ℚ) : ℝ)) := by
    norm_num [toRat_mul, toRat_ratOfNat, toRat_froSqCode,
      toMatrix_gramPowCode, toRat_ratPow, toRat_ratInvSucc,
      Fintype.card_fin] at hr ⊢
    simpa only [Nat.cast_pow] using hr
  exact_mod_cast hrat

/-- Soundness of the executable strict lower-third certificate. -/
theorem one_third_lt_opNorm_of_lowerThirdCert (d : ℕ) (A : MatrixCode)
    (m : ℕ) (h : lowerThirdCert d A m) :
    (1 : ℝ) / 3 < ‖toMatrix d A‖ := by
  apply OperatorNormCertificate.opNorm_gt_of_certificate
    (n := Fin (dim d)) ⟨⟨0, Nat.zero_lt_succ d⟩⟩ (toMatrix d A) m
  have hq := (ratLt_iff _ _).1 h
  have hr :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 2))
        (ratPow (ratInvSucc 2) (2 ^ (m + 2)))) : ℚ) : ℝ) <
        ((toRat (froSqCode d (gramPowCode d A m)) : ℚ) : ℝ)) := by
    exact_mod_cast hq
  norm_num [toRat_mul, toRat_ratOfNat, toRat_ratPow,
    toRat_ratInvSucc, toRat_froSqCode, toMatrix_gramPowCode,
    Fintype.card_fin] at hr ⊢
  simpa only [Nat.cast_pow] using hr

/-- Completeness of the executable strict lower-third certificate. -/
theorem exists_lowerThirdCert_of_one_third_lt_opNorm (d : ℕ)
    (A : MatrixCode) (h : (1 : ℝ) / 3 < ‖toMatrix d A‖) :
    ∃ m, lowerThirdCert d A m := by
  let i : Fin (dim d) := ⟨0, by simp [dim]⟩
  letI : Nonempty (Fin (dim d)) := ⟨i⟩
  obtain ⟨m, hm⟩ := OperatorNormCertificate.exists_certificate_of_lt_opNorm
    (n := Fin (dim d)) ⟨⟨0, Nat.zero_lt_succ d⟩⟩ (toMatrix d A)
    (show 0 ≤ (1 : ℝ) / 3 by positivity) h
  refine ⟨m, ?_⟩
  apply (ratLt_iff _ _).2
  have hr :
      ((((Fintype.card (Fin (dim d)) : ℕ) : ℝ) ^ 2 *
        ((1 : ℝ) / 3) ^ 2 ^ (m + 2)) <
        OperatorNormCertificate.froSq
          (((toMatrix d A)ᴴ * toMatrix d A) ^ 2 ^ m)) := hm
  have hrat :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 2))
        (ratPow (ratInvSucc 2) (2 ^ (m + 2)))) : ℚ) : ℝ) <
        ((toRat (froSqCode d (gramPowCode d A m)) : ℚ) : ℝ)) := by
    norm_num [toRat_mul, toRat_ratOfNat, toRat_ratPow,
      toRat_ratInvSucc, toRat_froSqCode, toMatrix_gramPowCode,
      Fintype.card_fin] at hr ⊢
    simpa only [Nat.cast_pow] using hr
  exact_mod_cast hrat

end EffectiveOperatorNormCode
end GroupApproximation
