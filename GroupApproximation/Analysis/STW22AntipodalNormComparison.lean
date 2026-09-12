import GroupApproximation.Analysis.STW22AntipodalBlockData
import GroupApproximation.Analysis.OperatorNormCertificate

/-!
# Coordinate norm comparison for the antipodal blocks

This file supplies the finite-rank estimate needed by the bounded uniform-two
completion.  Sharp constants are irrelevant: the existing operator-norm
certificate gives `‖M‖² ≤ card⁴ · froSq M`, while the normalized fibre trace
identifies `froSq M` with `card` times the squared fibre two-norm.  Thus the
cubic bound below is more than sufficient.
-/

namespace GroupApproximation
namespace STW22

open UniformTracialGNSTwoGauge UniformTracialTwoNullIdeal
open UniformTracialSequenceCompletion
open Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore
open OperatorNormCertificate
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open scoped CStarAlgebra ComplexOrder Matrix Matrix.Norms.L2Operator

noncomputable section

open CStarModule WithCStarModule in
/-- The C-star operator norm is bounded by the sum of the entry norms. -/
theorem cStarMatrix_norm_le_sum_norm
    {I : Type*} [Fintype I] (M : CStarMatrix I I ℂ) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v ↦ ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j

/-- The normalized matrix trace of `M⋆M` is its Frobenius mass divided by
the matrix size. -/
theorem matrixTracialState_star_mul_self_eq_froSq
    {I : Type*} [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (M : CStarMatrix I I ℂ) :
    (matrixTracialState complexTracialState I hI) (star M * M) =
      (((Fintype.card I : ℝ)⁻¹ * froSq M : ℝ) : ℂ) := by
  rw [matrixTracialState_apply]
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply]
  simp_rw [tracialState_complex_eq]
  push_cast
  congr 1
  rw [froSq]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

/-- Evaluation followed by the normalized fibre trace computes the same
Frobenius mass for a section of an antipodal block. -/
theorem fibreTracialState_star_mul_self_eq_froSq
    (d s : ℕ) (x : Sphere d) (a : RealProjectiveBlock d s) :
    fibreTracialState d s x (star a * a) =
      ((((s + 1 : ℕ) : ℝ)⁻¹ * froSq (a.1 x) : ℝ) : ℂ) := by
  rw [fibreTracialState, TracialState.compStarAlgHom_apply, map_mul, map_star]
  simpa using matrixTracialState_star_mul_self_eq_froSq
    (I := Fin (s + 1)) inferInstance (a.1 x)

/-- A deliberately crude but explicit comparison constant. -/
def antipodalCoordinateNormBound (n : ℕ) : ℝ :=
  (((antipodalBlockSize n + 1 : ℕ) : ℝ)) ^ 3

/-- The actual all-traces coordinate gauge controls the C-star norm on every
antipodal block. -/
theorem antipodalAllTracesGauge_isCoordinateNormComparison :
    IsCoordinateNormComparison antipodalAllTracesGauge
      antipodalCoordinateNormBound := by
  intro n a
  change ‖a.1‖ ≤ antipodalCoordinateNormBound n * antipodalAllTracesGauge.q n a
  have hbound0 : 0 ≤ antipodalCoordinateNormBound n := by
    exact pow_nonneg (Nat.cast_nonneg _) 3
  apply (ContinuousMap.norm_le _ (mul_nonneg hbound0
    (antipodalAllTracesGauge.nonneg n a))).2
  intro x
  let τ := fibreTracialState (antipodalBlockDimension n)
    (antipodalBlockSize n) x
  let q := antipodalAllTracesGauge.q n a
  let N : ℝ := ((antipodalBlockSize n + 1 : ℕ) : ℝ)
  have hN : 1 ≤ N := by
    have : 1 ≤ antipodalBlockSize n + 1 := by omega
    dsimp only [N]
    exact_mod_cast this
  have hq : 0 ≤ q := antipodalAllTracesGauge.nonneg n a
  have hτq : tracialTwoNorm τ a ≤ q := by
    change tracialTwoNorm τ a ≤ tracialTwoSize n a
    exact @tracialTwoNorm_le_tracialTwoSize AntipodalCounterexampleBlock
      inferInstance inferInstance
      (fun k ↦ nonemptyTracialState_antipodalCounterexampleBlock k) n τ a
  have htrace : tracialTwoNorm τ a =
      Real.sqrt (N⁻¹ * froSq (a.1 x)) := by
    rw [tracialTwoNorm_def,
      fibreTracialState_star_mul_self_eq_froSq]
    rfl
  rw [htrace] at hτq
  have hfro : froSq (a.1 x) ≤ N * q ^ 2 := by
    have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) hτq 2
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (by positivity))
      (froSq_nonneg _))] at hsquare
    have hN0 : N ≠ 0 := ne_of_gt (zero_lt_one.trans_le hN)
    calc
      froSq (a.1 x) = N * (N⁻¹ * froSq (a.1 x)) := by
        field_simp [hN0]
      _ ≤ N * q ^ 2 := mul_le_mul_of_nonneg_left hsquare (by positivity)
  have hentry : ∀ i j, ‖a.1 x i j‖ ≤ Real.sqrt (froSq (a.1 x)) := by
    intro i j
    calc
      ‖a.1 x i j‖ = Real.sqrt (‖a.1 x i j‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (froSq (a.1 x)) :=
        Real.sqrt_le_sqrt (sq_entry_le_froSq (a.1 x) i j)
  have hnorm : ‖a.1 x‖ ≤ N ^ 2 * Real.sqrt (froSq (a.1 x)) := by
    calc
      ‖a.1 x‖ ≤ ∑ j, ∑ i, ‖a.1 x i j‖ :=
        cStarMatrix_norm_le_sum_norm (a.1 x)
      _ ≤ ∑ _j : Fin (antipodalBlockSize n + 1),
          ∑ _i : Fin (antipodalBlockSize n + 1), Real.sqrt (froSq (a.1 x)) := by
        gcongr with j _ i _
        exact hentry i j
      _ = N ^ 2 * Real.sqrt (froSq (a.1 x)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        dsimp only [N]
        push_cast
        ring
  have hsqrt : Real.sqrt (froSq (a.1 x)) ≤ Real.sqrt (N * q ^ 2) :=
    Real.sqrt_le_sqrt hfro
  have hsqrtN : Real.sqrt (N * q ^ 2) ≤ N * q := by
    have hright : 0 ≤ N * q := mul_nonneg (by positivity) hq
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hright).mp
    rw [Real.sq_sqrt (mul_nonneg (by positivity) (sq_nonneg q))]
    nlinarith [sq_nonneg q]
  calc
    ‖a.1 x‖ ≤ N ^ 2 * Real.sqrt (froSq (a.1 x)) := hnorm
    _ ≤ N ^ 2 * Real.sqrt (N * q ^ 2) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ N ^ 2 * (N * q) :=
      mul_le_mul_of_nonneg_left hsqrtN (by positivity)
    _ = antipodalCoordinateNormBound n * q := by
      simp [antipodalCoordinateNormBound, N]
      ring

end

end STW22
end GroupApproximation
