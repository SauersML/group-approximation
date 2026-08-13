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

/-- The joint negative sector of two involutions. -/
noncomputable def jointExactInvolutionNegativeCut
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (Z R : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  exactInvolutionNegativeCut Z * exactInvolutionNegativeCut R

/-- Commuting self-adjoint involutions have an orthogonal joint negative
cut. -/
theorem jointExactInvolutionNegativeCut_isOrthogonalProjection
    {Y : Type*} [Fintype Y] [DecidableEq Y] (Z R : Matrix Y Y ℂ)
    (hZstar : Zᴴ = Z) (hZsq : Z * Z = 1)
    (hRstar : Rᴴ = R) (hRsq : R * R = 1)
    (hcomm : Z * R = R * Z) :
    KazhdanCornerMatrices.IsOrthogonalProjectionMatrix
      (jointExactInvolutionNegativeCut Z R) := by
  let P := exactInvolutionNegativeCut Z
  let Q := exactInvolutionNegativeCut R
  have hP := exactInvolutionNegativeCut_isOrthogonalProjection Z hZstar hZsq
  have hQ := exactInvolutionNegativeCut_isOrthogonalProjection R hRstar hRsq
  have hPidem : P * P = P := by simpa [P] using hP.2
  have hQidem : Q * Q = Q := by simpa [Q] using hQ.2
  have hPQ : P * Q = Q * P := by
    dsimp [P, Q, exactInvolutionNegativeCut]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    calc
      (1 - Z) * (1 - R) = 1 - Z - R + Z * R := by noncomm_ring
      _ = 1 - R - Z + R * Z := by rw [hcomm]; abel
      _ = (1 - R) * (1 - Z) := by noncomm_ring
  change KazhdanCornerMatrices.IsOrthogonalProjectionMatrix (P * Q)
  constructor
  · rw [Matrix.conjTranspose_mul, hP.1, hQ.1, hPQ]
  · calc
      (P * Q) * (P * Q) = P * (Q * P) * Q := by noncomm_ring
      _ = P * (P * Q) * Q := by rw [hPQ]
      _ = (P * P) * (Q * Q) := by noncomm_ring
      _ = P * Q := by rw [hPidem, hQidem]

/-- Under the regular character of the generated `C₂ × C₂`, the joint
negative cut has normalized trace `1/4`. -/
theorem normTrace_jointExactInvolutionNegativeCut
    (Y : FiniteModel) (Z R : Matrix Y Y ℂ)
    (hY : 0 < Fintype.card Y)
    (hZ : normTrace Y Z = 0)
    (hR : normTrace Y R = 0)
    (hZR : normTrace Y (Z * R) = 0) :
    normTrace Y (jointExactInvolutionNegativeCut Z R) = (4 : ℂ)⁻¹ := by
  have hcard : (Fintype.card Y : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hY)
  have htrZ : Matrix.trace Z = 0 := by
    apply (div_eq_zero_iff).mp hZ |>.resolve_right
    exact hcard
  have htrR : Matrix.trace R = 0 := by
    apply (div_eq_zero_iff).mp hR |>.resolve_right
    exact hcard
  have htrZR : Matrix.trace (Z * R) = 0 := by
    apply (div_eq_zero_iff).mp hZR |>.resolve_right
    exact hcard
  simp only [jointExactInvolutionNegativeCut, exactInvolutionNegativeCut]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, normTrace,
    Matrix.trace_smul, smul_eq_mul]
  have hexpand : (1 - Z) * (1 - R) = 1 - Z - R + Z * R := by
    noncomm_ring
  rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_one, htrZ, htrR, htrZR, sub_zero, sub_zero, add_zero]
  field_simp
  norm_num

/-- An anticommuting involution flips the negative cut of the other
involution to its complementary cut. -/
theorem exactInvolutionNegativeCut_conj_of_anticommute
    {Y : Type*} [Fintype Y] [DecidableEq Y] (R Z : Matrix Y Y ℂ)
    (hRsq : R * R = 1) (hanti : R * Z = -(Z * R)) :
    R * exactInvolutionNegativeCut Z * R =
      1 - exactInvolutionNegativeCut Z := by
  unfold exactInvolutionNegativeCut
  rw [Matrix.mul_smul, Matrix.smul_mul]
  calc
    (2 : ℂ)⁻¹ • (R * (1 - Z) * R) =
        (2 : ℂ)⁻¹ • (1 + Z) := by
          congr 1
          calc
            R * (1 - Z) * R = R * R - (R * Z) * R := by noncomm_ring
            _ = R * R + Z * (R * R) := by rw [hanti]; noncomm_ring
            _ = 1 + Z := by simp only [hRsq, Matrix.mul_one]
    _ = 1 - (2 : ℂ)⁻¹ • (1 - Z) := by
      module

/-- The original negative cut and its anticommuting conjugate are
orthogonal. -/
theorem exactInvolutionNegativeCut_mul_conj_eq_zero
    {Y : Type*} [Fintype Y] [DecidableEq Y] (R Z : Matrix Y Y ℂ)
    (hZstar : Zᴴ = Z) (hZsq : Z * Z = 1)
    (hRsq : R * R = 1) (hanti : R * Z = -(Z * R)) :
    exactInvolutionNegativeCut Z *
        (R * exactInvolutionNegativeCut Z * R) = 0 := by
  rw [exactInvolutionNegativeCut_conj_of_anticommute R Z hRsq hanti]
  have hP := (exactInvolutionNegativeCut_isOrthogonalProjection
    Z hZstar hZsq).2
  rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]

/-- The two Pauli halves exactly fill their common carrier. -/
theorem exactInvolutionNegativeCut_add_conj_eq_one
    {Y : Type*} [Fintype Y] [DecidableEq Y] (R Z : Matrix Y Y ℂ)
    (hRsq : R * R = 1) (hanti : R * Z = -(Z * R)) :
    exactInvolutionNegativeCut Z +
        R * exactInvolutionNegativeCut Z * R = 1 := by
  rw [exactInvolutionNegativeCut_conj_of_anticommute R Z hRsq hanti]
  abel

end GroupApproximation
