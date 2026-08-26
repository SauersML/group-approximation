import GroupApproximation.Computability.EffectiveMatrixCode

/-!
# Executable strict upper certificates for matrix operator norm

The analytic certificate in `OperatorNormCertificate` uses the Frobenius
quantity of repeated squares of `Aᴴ A`.  All entries remain Gaussian rational,
so the certificate is a single decidable rational inequality.  Repeated
squaring is essential: unlike a one-step entrywise bound, this test is both
sound and complete for every strict operator-norm inequality, independently
of the matrix dimension.
-/

namespace GroupApproximation
namespace EffectiveMatrixNormCertificate

open RationalComplexCode EffectiveMatrixCode
open scoped Matrix Matrix.Norms.L2Operator

/-- Sum of squared entry norms, computed entirely in rational codes. -/
def matrixFroSq (d : ℕ) (A : MatrixCode) : RatCode :=
  (List.range (dim d)).foldl (fun q i =>
    (List.range (dim d)).foldl (fun r j =>
      ratAdd r (complexNormSq (entry d A i j))) q) ratZero

/-- Iterate the squaring operation `m` times. -/
def squareIter (d : ℕ) : ℕ → MatrixCode → MatrixCode
  | 0, A => A
  | m + 1, A => squareIter d m (matrixMul d A A)

/-- The coded matrix `(Aᴴ A) ^ (2 ^ m)`. -/
def certificateMatrix (d : ℕ) (A : MatrixCode) (m : ℕ) : MatrixCode :=
  squareIter d m (matrixMul d (conjTranspose d A) A)

/-- A natural `m` certifies `‖A‖ < 1 / (k + 1)` by the repeated-square
Frobenius inequality from `OperatorNormCertificate`. -/
def upperNormWitness (d k : ℕ) (A : MatrixCode) (m : ℕ) : Prop :=
  RatLt
    (ratMul
      (ratOfNat ((k + 1) ^ (2 ^ (m + 2)) * (dim d) ^ 4))
      (matrixFroSq d (certificateMatrix d A m)))
    ratOne

instance upperNormWitnessDecidable (d k : ℕ) (A : MatrixCode) (m : ℕ) :
    Decidable (upperNormWitness d k A m) := by
  unfold upperNormWitness
  infer_instance

theorem matrixFroSq_semantics (d : ℕ) (A : MatrixCode) :
    (toRat (matrixFroSq d A) : ℝ) =
      OperatorNormCertificate.froSq (toMatrix d A) := by
  simp only [matrixFroSq, OperatorNormCertificate.froSq]
  rw [toRat_foldl]
  simp only [toRat_zero, zero_add, List.map_map, Function.comp_apply]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [toRat_foldl]
  simp only [List.map_map, Function.comp_apply]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    Finset.sum_range]
  push_cast
  simp only [toRat_complexNormSq, toMatrix]

theorem toMatrix_squareIter (d : ℕ) (A : MatrixCode) : ∀ m : ℕ,
    toMatrix d (squareIter d m A) = (toMatrix d A) ^ (2 ^ m)
  | 0 => by simp [squareIter]
  | m + 1 => by
      rw [squareIter, toMatrix_squareIter, toMatrix_mul]
      rw [pow_succ, pow_mul]
      simp only [pow_two]

theorem toMatrix_certificateMatrix (d : ℕ) (A : MatrixCode) (m : ℕ) :
    toMatrix d (certificateMatrix d A m) =
      ((toMatrix d A)ᴴ * toMatrix d A) ^ (2 ^ m) := by
  rw [certificateMatrix, toMatrix_squareIter, toMatrix_mul,
    toMatrix_conjTranspose]

/-- Soundness of the executable upper certificate. -/
theorem opNorm_lt_of_upperNormWitness (d k : ℕ) (A : MatrixCode) (m : ℕ)
    (h : upperNormWitness d k A m) :
    ‖toMatrix d A‖ < 1 / ((k : ℝ) + 1) := by
  have hcert :
      ((Fintype.card (Fin (dim d)) : ℕ) : ℝ) ^ 4 *
          OperatorNormCertificate.froSq
            (((toMatrix d A)ᴴ * toMatrix d A) ^ (2 ^ m)) <
        (1 / ((k : ℝ) + 1)) ^ (2 ^ (m + 2)) := by
    rw [upperNormWitness, ratLt_iff] at h
    rw [toRat_mul, toRat_ratOfNat, toRat_one,
      matrixFroSq_semantics, toMatrix_certificateMatrix] at h
    have hreal :
        ((((k + 1) ^ (2 ^ (m + 2)) * (dim d) ^ 4 : ℕ) : ℚ) *
          toRat (matrixFroSq d (certificateMatrix d A m)) : ℚ) < 1 := h
    have hcast :
        (((((k + 1) ^ (2 ^ (m + 2)) * (dim d) ^ 4 : ℕ) : ℚ) *
          toRat (matrixFroSq d (certificateMatrix d A m)) : ℚ) : ℝ) < 1 := by
      exact_mod_cast hreal
    rw [matrixFroSq_semantics, toMatrix_certificateMatrix] at hcast
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Fintype.card_fin] at hcast ⊢
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [one_div, inv_pow]
    rw [lt_inv_iff₀' (pow_pos hkpos _)]
    nlinarith
  exact OperatorNormCertificate.opNorm_lt_of_certificate
    (toMatrix d A) (by positivity) m hcert

/-- Completeness of the executable upper certificate. -/
theorem exists_upperNormWitness_of_opNorm_lt (d k : ℕ) (A : MatrixCode)
    (h : ‖toMatrix d A‖ < 1 / ((k : ℝ) + 1)) :
    ∃ m : ℕ, upperNormWitness d k A m := by
  obtain ⟨m, hm⟩ := OperatorNormCertificate.exists_certificate_of_opNorm_lt
    (toMatrix d A) (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)) h
  refine ⟨m, ?_⟩
  rw [upperNormWitness, ratLt_iff]
  rw [toRat_mul, toRat_ratOfNat, toRat_one]
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hscaled :
      (((k : ℝ) + 1) ^ (2 ^ (m + 2)) * (dim d : ℝ) ^ 4) *
          OperatorNormCertificate.froSq
            (((toMatrix d A)ᴴ * toMatrix d A) ^ (2 ^ m)) < 1 := by
    rw [one_div, inv_pow] at hm
    exact (lt_inv_iff₀' (pow_pos hkpos _)).1 (by
      simpa [Fintype.card_fin, mul_assoc, mul_left_comm, mul_comm] using hm)
  have hreal :
      ((((k + 1) ^ (2 ^ (m + 2)) * (dim d) ^ 4 : ℕ) : ℝ) *
        (toRat (matrixFroSq d (certificateMatrix d A m)) : ℝ)) < 1 := by
    rw [matrixFroSq_semantics, toMatrix_certificateMatrix]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hscaled
  exact_mod_cast hreal

end EffectiveMatrixNormCertificate
end GroupApproximation
