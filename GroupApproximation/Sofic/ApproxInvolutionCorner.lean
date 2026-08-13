import GroupApproximation.Sofic.KazhdanCornerMatrices

/-!
# Spectral rounding of an approximate matrix involution

The marked-compression obstruction cuts an operator-norm approximation by the
negative spectral sector of a central involution.  This file supplies the
exact finite-dimensional objects used in that cut.  Quantitative proximity to
the original approximate involution is proved in the subsequent analytic
layer; here the spectral projections and rounded sign are exact.
-/

namespace GroupApproximation
namespace ApproxInvolutionCorner

open Matrix
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Hermitian part of a square complex matrix. -/
noncomputable def hermitianPart (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  ((2 : ℂ)⁻¹) • (U + Uᴴ)

omit [Fintype Y] [DecidableEq Y] in
/-- The Hermitian part is exactly self-adjoint. -/
theorem hermitianPart_conjTranspose (U : Matrix Y Y ℂ) :
    (hermitianPart U)ᴴ = hermitianPart U := by
  rw [hermitianPart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  rw [hstar, add_comm]

omit [Fintype Y] [DecidableEq Y] in
/-- The Hermitian part, in Mathlib's predicate form. -/
theorem hermitianPart_isHermitian (U : Matrix Y Y ℂ) :
    (hermitianPart U).IsHermitian :=
  hermitianPart_conjTranspose U

/-- For a unitary matrix, failure to be self-adjoint is exactly its
involution defect.  Right multiplication by `Uᴴ` is isometric. -/
theorem norm_sub_conjTranspose_eq_norm_sq_sub_one
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    ‖U - Uᴴ‖ = ‖U * U - 1‖ := by
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hU
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  have hfactor : U - Uᴴ = (U * U - 1) * Uᴴ := by
    calc
      U - Uᴴ = U * (U * Uᴴ) - Uᴴ := by rw [hUUstar, Matrix.mul_one]
      _ = (U * U - 1) * Uᴴ := by noncomm_ring
  rw [hfactor, CStarRing.norm_mul_mem_unitary _ hUstar]

/-- Hermitian symmetrization costs exactly half the operator-norm
involution defect of a unitary. -/
theorem norm_hermitianPart_sub_eq_half_sq_defect
    (U : Matrix Y Y ℂ) (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    ‖hermitianPart U - U‖ =
      (1 / 2 : ℝ) * ‖U * U - 1‖ := by
  have hrewrite : hermitianPart U - U =
      ((2 : ℂ)⁻¹) • (Uᴴ - U) := by
    rw [hermitianPart]
    module
  rw [hrewrite, norm_smul]
  have hscalar : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar, show Uᴴ - U = -(U - Uᴴ) by abel, norm_neg,
    norm_sub_conjTranspose_eq_norm_sq_sub_one U hU]

/-- Positive spectral projection of the Hermitian part, with threshold zero. -/
noncomputable def positiveProjection (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  KazhdanCornerMatrices.spectralAbove (hermitianPart U)
    (hermitianPart_isHermitian U) 0

/-- Negative spectral projection, complementary to `positiveProjection`. -/
noncomputable def negativeProjection (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  1 - positiveProjection U

/-- The positive spectral cutoff is an orthogonal projection. -/
theorem positiveProjection_isOrthogonalProjection (U : Matrix Y Y ℂ) :
    KazhdanCornerMatrices.IsOrthogonalProjectionMatrix
      (positiveProjection U) :=
  KazhdanCornerMatrices.spectralAbove_isOrthogonalProjection
    (hermitianPart U) (hermitianPart_isHermitian U) 0

/-- The negative spectral cutoff is an orthogonal projection. -/
theorem negativeProjection_isOrthogonalProjection (U : Matrix Y Y ℂ) :
    KazhdanCornerMatrices.IsOrthogonalProjectionMatrix
      (negativeProjection U) := by
  exact KazhdanCornerMatrices.one_sub_isOrthogonalProjection
    (positiveProjection_isOrthogonalProjection U)

/-- The two spectral sectors sum to the identity. -/
theorem positiveProjection_add_negativeProjection (U : Matrix Y Y ℂ) :
    positiveProjection U + negativeProjection U = 1 := by
  simp [negativeProjection]

/-- The two spectral sectors are orthogonal. -/
theorem positiveProjection_mul_negativeProjection (U : Matrix Y Y ℂ) :
    positiveProjection U * negativeProjection U = 0 := by
  rw [negativeProjection, Matrix.mul_sub, Matrix.mul_one,
    (positiveProjection_isOrthogonalProjection U).2, sub_self]

/-- Orthogonality in the reverse order. -/
theorem negativeProjection_mul_positiveProjection (U : Matrix Y Y ℂ) :
    negativeProjection U * positiveProjection U = 0 := by
  rw [negativeProjection, Matrix.sub_mul, Matrix.one_mul,
    (positiveProjection_isOrthogonalProjection U).2, sub_self]

/-- Exact sign of the Hermitian part: `+1` on the positive sector and `-1`
on its complement. -/
noncomputable def roundedInvolution (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (2 : ℂ) • positiveProjection U - 1

/-- The rounded sign is self-adjoint. -/
theorem roundedInvolution_conjTranspose (U : Matrix Y Y ℂ) :
    (roundedInvolution U)ᴴ = roundedInvolution U := by
  rw [roundedInvolution, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    (positiveProjection_isOrthogonalProjection U).1]
  norm_num

/-- The rounded sign squares exactly to the identity. -/
theorem roundedInvolution_sq (U : Matrix Y Y ℂ) :
    roundedInvolution U * roundedInvolution U = 1 := by
  rw [roundedInvolution]
  have hP := (positiveProjection_isOrthogonalProjection U).2
  simp only [two_smul]
  calc
    (positiveProjection U + positiveProjection U - 1) *
          (positiveProjection U + positiveProjection U - 1) =
        positiveProjection U * positiveProjection U +
          positiveProjection U * positiveProjection U +
          positiveProjection U * positiveProjection U +
          positiveProjection U * positiveProjection U -
          positiveProjection U - positiveProjection U -
          positiveProjection U - positiveProjection U + 1 := by
            noncomm_ring
    _ = 1 := by rw [hP]; abel

/-- The rounded sign is an exact unitary matrix. -/
theorem roundedInvolution_mem_unitaryGroup (U : Matrix Y Y ℂ) :
    roundedInvolution U ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    roundedInvolution_conjTranspose, roundedInvolution_sq]

/-- The negative projection is `(1-Z)/2` for the rounded involution `Z`. -/
theorem negativeProjection_eq_one_sub_rounded (U : Matrix Y Y ℂ) :
    negativeProjection U =
      ((2 : ℂ)⁻¹) • (1 - roundedInvolution U) := by
  simp [negativeProjection, roundedInvolution]
  module

/-- A vanishing negative sector forces the rounded involution to be the
identity. -/
theorem roundedInvolution_eq_one_of_negativeProjection_eq_zero
    (U : Matrix Y Y ℂ) (hneg : negativeProjection U = 0) :
    roundedInvolution U = 1 := by
  have h := negativeProjection_eq_one_sub_rounded U
  rw [hneg] at h
  have hscalar : ((2 : ℂ)⁻¹) ≠ 0 := by norm_num
  have hone : 1 - roundedInvolution U = 0 := by
    exact (smul_eq_zero.mp h.symm).resolve_left hscalar
  exact (sub_eq_zero.mp hone).symm

/-- The rounded involution acts by `-1` on its negative sector. -/
theorem roundedInvolution_mul_negativeProjection (U : Matrix Y Y ℂ) :
    roundedInvolution U * negativeProjection U = -negativeProjection U := by
  rw [roundedInvolution, negativeProjection]
  have hP := (positiveProjection_isOrthogonalProjection U).2
  simp only [two_smul]
  calc
    (positiveProjection U + positiveProjection U - 1) *
          (1 - positiveProjection U) =
        positiveProjection U + positiveProjection U -
          positiveProjection U * positiveProjection U -
          positiveProjection U * positiveProjection U - 1 +
          positiveProjection U := by noncomm_ring
    _ = -(1 - positiveProjection U) := by rw [hP]; abel

end ApproxInvolutionCorner
end GroupApproximation
