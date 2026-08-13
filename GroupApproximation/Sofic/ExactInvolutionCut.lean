import GroupApproximation.Sofic.KazhdanCornerMatrices
import GroupApproximation.Sofic.PhasePropagation

/-!
# The exact negative cut of a tracial involution

An exact self-adjoint involution `R` has an algebraically defined negative
spectral cut `(1 - R) / 2`.  This file records the two facts needed by the raw
compressor audit: the cut is an orthogonal projection, and trace zero of `R`
forces the cut to have normalized trace `1 / 2`.
-/

namespace GroupApproximation

open Matrix

/-- The negative spectral cut of an exact involution, written without spectral
calculus. -/
noncomputable def exactInvolutionNegativeCut {Y : Type*} [Fintype Y]
    [DecidableEq Y] (R : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (2 : ℂ)⁻¹ • (1 - R)

/-- The affine negative cut of a self-adjoint involution is an orthogonal
projection. -/
theorem exactInvolutionNegativeCut_isOrthogonalProjection
    {Y : Type*} [Fintype Y] [DecidableEq Y] (R : Matrix Y Y ℂ)
    (hstar : Rᴴ = R) (hsq : R * R = 1) :
    KazhdanCornerMatrices.IsOrthogonalProjectionMatrix
      (exactInvolutionNegativeCut R) := by
  constructor
  · rw [exactInvolutionNegativeCut, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar]
    norm_num
  · rw [exactInvolutionNegativeCut, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    calc
      ((2 : ℂ)⁻¹ * 2⁻¹) • ((1 - R) * (1 - R)) =
          ((2 : ℂ)⁻¹ * 2⁻¹) • ((2 : ℂ) • (1 - R)) := by
            congr 1
            calc
              (1 - R) * (1 - R) = 1 - R - R + R * R := by noncomm_ring
              _ = (2 : ℂ) • (1 - R) := by rw [hsq]; module
      _ = (2 : ℂ)⁻¹ • (1 - R) := by norm_num [smul_smul]

/-- A trace-zero involution has a trace-half negative cut. -/
theorem normTrace_exactInvolutionNegativeCut
    (Y : FiniteModel) (R : Matrix Y Y ℂ)
    (hY : 0 < Fintype.card Y) (htrace : normTrace Y R = 0) :
    normTrace Y (exactInvolutionNegativeCut R) = (2 : ℂ)⁻¹ := by
  rw [exactInvolutionNegativeCut, normTrace, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_one, smul_eq_mul]
  have hcard : (Fintype.card Y : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hY)
  have htr : Matrix.trace R = 0 := by
    apply (div_eq_zero_iff).mp htrace |>.resolve_right
    exact hcard
  rw [htr, sub_zero]
  field_simp

end GroupApproximation
