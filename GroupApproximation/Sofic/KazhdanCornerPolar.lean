import GroupApproximation.Sofic.KazhdanCornerMatrices

/-!
# Polar correction for finite matrix corners

The compression of a unitary to an almost invariant spectral subspace is an
almost-unitary square matrix.  This file gives the exact finite-dimensional
polar correction used by the Kazhdan-corner construction.  It is written in
the eigenbasis of `Cᴴ * C`, so no choice of singular-value decomposition is
needed beyond Mathlib's Hermitian spectral theorem.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y]

/-- The positive Gram matrix of a square complex matrix. -/
def cornerGram (C : Matrix Y Y ℂ) : Matrix Y Y ℂ := Cᴴ * C

theorem cornerGram_isHermitian (C : Matrix Y Y ℂ) :
    (cornerGram C).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self C

variable [DecidableEq Y]

/-- Diagonal matrix of the real eigenvalues of a Hermitian matrix. -/
noncomputable def hermitianEigenvalueDiagonal {P : Matrix Y Y ℂ}
    (hP : P.IsHermitian) : Matrix Y Y ℂ :=
  Matrix.diagonal fun i ↦ (hP.eigenvalues i : ℂ)

/-- Diagonal reciprocal square roots of the eigenvalues of a Hermitian
matrix. -/
noncomputable def hermitianInvSqrtDiagonal {P : Matrix Y Y ℂ}
    (hP : P.IsHermitian) : Matrix Y Y ℂ :=
  Matrix.diagonal fun i ↦ ((Real.sqrt (hP.eigenvalues i) : ℝ) : ℂ)⁻¹

theorem hermitianInvSqrtDiagonal_conjTranspose {P : Matrix Y Y ℂ}
    (hP : P.IsHermitian) :
    (hermitianInvSqrtDiagonal hP)ᴴ = hermitianInvSqrtDiagonal hP := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hermitianInvSqrtDiagonal, Matrix.conjTranspose_apply]
  · simp [hermitianInvSqrtDiagonal, Matrix.conjTranspose_apply, hij,
      Ne.symm hij]

theorem hermitianInvSqrtDiagonal_mul_eigenvalueDiagonal
    {P : Matrix Y Y ℂ} (hP : P.IsHermitian)
    (hpos : ∀ i, 0 < hP.eigenvalues i) :
    hermitianInvSqrtDiagonal hP * hermitianEigenvalueDiagonal hP *
        hermitianInvSqrtDiagonal hP = 1 := by
  rw [hermitianInvSqrtDiagonal, hermitianEigenvalueDiagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hlambda : 0 < hP.eigenvalues i := hpos i
    have hsqrt : Real.sqrt (hP.eigenvalues i) ≠ 0 :=
      (Real.sqrt_pos.2 hlambda).ne'
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have hsqrtSq :
        ((Real.sqrt (hP.eigenvalues i) : ℂ) ^ 2) =
          (hP.eigenvalues i : ℂ) := by
      exact_mod_cast Real.sq_sqrt hlambda.le
    rw [show ((Real.sqrt (hP.eigenvalues i) : ℂ)⁻¹ *
        (hP.eigenvalues i : ℂ) *
        (Real.sqrt (hP.eigenvalues i) : ℂ)⁻¹) =
        (hP.eigenvalues i : ℂ) /
          (Real.sqrt (hP.eigenvalues i) : ℂ) ^ 2 by field_simp]
    rw [hsqrtSq, div_self]
    exact_mod_cast hlambda.ne'
  · simp [hij]

/-- An eigenvalue of a Hermitian matrix differs from `1` by at most the
operator norm of `P - 1`. -/
theorem abs_hermitianEigenvalue_sub_one_le {P : Matrix Y Y ℂ}
    (hP : P.IsHermitian) (i : Y) :
    |hP.eigenvalues i - 1| ≤ ‖P - 1‖ := by
  let x : EuclideanSpace ℂ Y := hP.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hP.eigenvectorBasis.orthonormal.1 i
  have heigen :
      (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (P - 1) x =
        ((hP.eigenvalues i - 1 : ℝ) : ℂ) • x := by
    apply PiLp.ext
    intro j
    change ((P - 1) *ᵥ (x : Y → ℂ)) j =
      (((hP.eigenvalues i - 1 : ℝ) : ℂ) • (x : Y → ℂ)) j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have hi := congrFun (hP.mulVec_eigenvectorBasis i) j
    change (P *ᵥ (x : Y → ℂ)) j - (x : Y → ℂ) j = _
    rw [hi]
    simp
    ring
  calc
    |hP.eigenvalues i - 1| =
        ‖((hP.eigenvalues i - 1 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖P - 1‖ := by
      simpa only [heigen, norm_smul, hx, mul_one,
        Matrix.l2_opNorm_toEuclideanCLM] using
        ContinuousLinearMap.le_opNorm
          ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (P - 1)) x

/-- Uniform scalar estimate for reciprocal square roots near `1`. -/
theorem abs_inv_sqrt_sub_one_le_two_mul {lambda delta : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : |lambda - 1| ≤ delta) :
    |(Real.sqrt lambda)⁻¹ - 1| ≤ 2 * delta := by
  let r := Real.sqrt lambda
  have hr0 : 0 ≤ r := Real.sqrt_nonneg lambda
  have hrsq : r ^ 2 = lambda := Real.sq_sqrt hlambda.le
  have hlower : 1 / 2 ≤ lambda := by
    have := (neg_le_of_abs_le hclose)
    linarith only [this, hdeltaHalf]
  have hrhalf : 1 / 2 ≤ r := by
    nlinarith only [hrsq, hlower, hr0]
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hrhalf
  rcases le_total r 1 with hrle | honele
  · have hnumer : 0 ≤ 1 - r := sub_nonneg.mpr hrle
    have hsmall : 1 - r ≤ delta := by
      have hbelow := neg_le_of_abs_le hclose
      nlinarith only [hbelow, hrsq,
        mul_nonneg hr0 (sub_nonneg.mpr hrle)]
    rw [show r⁻¹ - 1 = (1 - r) / r by field_simp]
    rw [abs_of_nonneg (div_nonneg hnumer hr0), div_le_iff₀ hrpos]
    nlinarith only [hsmall, hrhalf, hdelta]
  · have hnonpos : r⁻¹ - 1 ≤ 0 :=
      sub_nonpos.mpr ((inv_le_one₀ hrpos).2 honele)
    have hsmall : r - 1 ≤ delta := by
      have hupper := le_of_abs_le hclose
      nlinarith only [hupper, hrsq, honele]
    rw [abs_of_nonpos hnonpos]
    rw [show -(r⁻¹ - 1) = (r - 1) / r by field_simp; ring]
    rw [div_le_iff₀ hrpos]
    nlinarith only [hsmall, hrhalf, hdelta]

/-- A Gram matrix within `1/2` of the identity has strictly positive
spectrum. -/
theorem cornerGram_eigenvalues_pos_of_norm_sub_one_le
    (C : Matrix Y Y ℂ) (hP : (cornerGram C).IsHermitian) {delta : ℝ}
    (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram C - 1‖ ≤ delta) :
    ∀ i, 0 < hP.eigenvalues i := by
  intro i
  have habs : |hP.eigenvalues i - 1| ≤ delta :=
    (abs_hermitianEigenvalue_sub_one_le hP i).trans hclose
  have hbelow := neg_le_of_abs_le habs
  linarith only [hbelow, hdeltaHalf]

/-- The diagonal inverse-square-root correction is uniformly close to the
identity when the underlying Hermitian matrix is. -/
theorem norm_hermitianInvSqrtDiagonal_sub_one_le
    {P : Matrix Y Y ℂ} (hP : P.IsHermitian) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖P - 1‖ ≤ delta) :
    ‖hermitianInvSqrtDiagonal hP - 1‖ ≤ 2 * delta := by
  have hpos : ∀ i, 0 < hP.eigenvalues i := by
    intro i
    have habs : |hP.eigenvalues i - 1| ≤ delta :=
      (abs_hermitianEigenvalue_sub_one_le hP i).trans hclose
    have hbelow := neg_le_of_abs_le habs
    linarith only [hbelow, hdeltaHalf]
  have hdiag : hermitianInvSqrtDiagonal hP - 1 =
      Matrix.diagonal (fun i ↦
        ((Real.sqrt (hP.eigenvalues i) : ℂ)⁻¹ - 1)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hermitianInvSqrtDiagonal]
    · simp [hermitianInvSqrtDiagonal, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [show (Real.sqrt (hP.eigenvalues i) : ℂ)⁻¹ - 1 =
      (((Real.sqrt (hP.eigenvalues i))⁻¹ - 1 : ℝ) : ℂ) by
        push_cast
        rfl,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_inv_sqrt_sub_one_le_two_mul (hpos i) hdelta hdeltaHalf
    ((abs_hermitianEigenvalue_sub_one_le hP i).trans hclose)

/-- The inverse square root of `Cᴴ * C`, defined spectrally.  The definition
is total; exact unitarity of the corrected matrix requires positivity of all
Gram eigenvalues. -/
noncomputable def cornerGramInvSqrt (C : Matrix Y Y ℂ)
    (hP : (cornerGram C).IsHermitian) : Matrix Y Y ℂ :=
  let U : Matrix Y Y ℂ := hP.eigenvectorUnitary
  U * hermitianInvSqrtDiagonal hP * Uᴴ

/-- The full inverse-square-root correction has the same dimension-free
distance bound as its diagonal form. -/
theorem norm_cornerGramInvSqrt_sub_one_le
    (C : Matrix Y Y ℂ) (hP : (cornerGram C).IsHermitian) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram C - 1‖ ≤ delta) :
    ‖cornerGramInvSqrt C hP - 1‖ ≤ 2 * delta := by
  let U : Matrix Y Y ℂ := hP.eigenvectorUnitary
  let D : Matrix Y Y ℂ := hermitianInvSqrtDiagonal hP
  have hU : U ∈ Matrix.unitaryGroup Y ℂ := hP.eigenvectorUnitary.2
  have hUUstar : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have hrewrite : cornerGramInvSqrt C hP - 1 = U * (D - 1) * Uᴴ := by
    change U * D * Uᴴ - 1 = U * (D - 1) * Uᴴ
    calc
      U * D * Uᴴ - 1 = U * D * Uᴴ - U * Uᴴ := by rw [hUUstar]
      _ = U * (D - 1) * Uᴴ := by noncomm_ring
  rw [hrewrite]
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  rw [CStarRing.norm_mul_mem_unitary _ hUstar,
    CStarRing.norm_mem_unitary_mul _ hU]
  exact norm_hermitianInvSqrtDiagonal_sub_one_le hP hdelta hdeltaHalf hclose

/-- Cancellation of the two intermediate unitary basis changes in a product
of three conjugated matrices. -/
theorem unitary_conjugate_three_mul {U D L : Matrix Y Y ℂ}
    (hUU : Uᴴ * U = 1) :
    (U * D * Uᴴ) * (U * L * Uᴴ) * (U * D * Uᴴ) =
      U * (D * L * D) * Uᴴ := by
  calc
    (U * D * Uᴴ) * (U * L * Uᴴ) * (U * D * Uᴴ) =
        U * D * (Uᴴ * U) * L * (Uᴴ * U) * D * Uᴴ := by
          noncomm_ring
    _ = U * (D * L * D) * Uᴴ := by rw [hUU]; noncomm_ring

/-- Right polar correction of a square matrix. -/
noncomputable def polarCorrect (C : Matrix Y Y ℂ)
    (hP : (cornerGram C).IsHermitian) : Matrix Y Y ℂ :=
  C * cornerGramInvSqrt C hP

/-- If the Gram matrix has strictly positive spectrum, `polarCorrect C` is
exactly unitary. -/
theorem polarCorrect_mem_unitaryGroup (C : Matrix Y Y ℂ)
    (hP : (cornerGram C).IsHermitian)
    (hpos : ∀ i, 0 < hP.eigenvalues i) :
    polarCorrect C hP ∈ Matrix.unitaryGroup Y ℂ := by
  let U : Matrix Y Y ℂ := hP.eigenvectorUnitary
  have hUU : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2
  have hPdiag : cornerGram C =
      U * hermitianEigenvalueDiagonal hP * Uᴴ := by
    calc
      cornerGram C = Unitary.conjStarAlgAut ℂ _ hP.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)) :=
        hP.spectral_theorem
      _ = U * hermitianEigenvalueDiagonal hP * Uᴴ := by
        rfl
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (polarCorrect C hP)ᴴ * polarCorrect C hP = 1
  rw [polarCorrect, Matrix.conjTranspose_mul]
  rw [show (cornerGramInvSqrt C hP)ᴴ * Cᴴ *
      (C * cornerGramInvSqrt C hP) =
        (cornerGramInvSqrt C hP)ᴴ * (Cᴴ * C) *
          cornerGramInvSqrt C hP by simp only [mul_assoc]]
  change (U * hermitianInvSqrtDiagonal hP * Uᴴ)ᴴ * cornerGram C *
    (U * hermitianInvSqrtDiagonal hP * Uᴴ) = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    hermitianInvSqrtDiagonal_conjTranspose]
  rw [← mul_assoc U (hermitianInvSqrtDiagonal hP) Uᴴ]
  have hreplace :
      (U * hermitianInvSqrtDiagonal hP * Uᴴ) * cornerGram C *
          (U * hermitianInvSqrtDiagonal hP * Uᴴ) =
        (U * hermitianInvSqrtDiagonal hP * Uᴴ) *
          (U * hermitianEigenvalueDiagonal hP * Uᴴ) *
          (U * hermitianInvSqrtDiagonal hP * Uᴴ) :=
    congrArg (fun P : Matrix Y Y ℂ ↦
      (U * hermitianInvSqrtDiagonal hP * Uᴴ) * P *
        (U * hermitianInvSqrtDiagonal hP * Uᴴ)) hPdiag
  rw [hreplace]
  calc
    (U * hermitianInvSqrtDiagonal hP * Uᴴ) *
        (U * hermitianEigenvalueDiagonal hP * Uᴴ) *
        (U * hermitianInvSqrtDiagonal hP * Uᴴ) =
        U * (hermitianInvSqrtDiagonal hP *
          hermitianEigenvalueDiagonal hP *
          hermitianInvSqrtDiagonal hP) * Uᴴ :=
      unitary_conjugate_three_mul hUU
    _ = U * Uᴴ := by
      rw [hermitianInvSqrtDiagonal_mul_eigenvalueDiagonal hP hpos]
      simp
    _ = 1 := hUUstar

/-- Polar correction changes a matrix by at most its norm times twice its
Gram defect from the identity. -/
theorem norm_polarCorrect_sub_le_mul
    (C : Matrix Y Y ℂ) (hP : (cornerGram C).IsHermitian) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram C - 1‖ ≤ delta) :
    ‖polarCorrect C hP - C‖ ≤ ‖C‖ * (2 * delta) := by
  have hrewrite : polarCorrect C hP - C =
      C * (cornerGramInvSqrt C hP - 1) := by
    rw [polarCorrect, Matrix.mul_sub, Matrix.mul_one]
  rw [hrewrite]
  calc
    ‖C * (cornerGramInvSqrt C hP - 1)‖ ≤
        ‖C‖ * ‖cornerGramInvSqrt C hP - 1‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ ‖C‖ * (2 * delta) := mul_le_mul_of_nonneg_left
      (norm_cornerGramInvSqrt_sub_one_le C hP hdelta hdeltaHalf hclose)
      (norm_nonneg _)

/-- For a contraction, the polar correction is at most twice the Gram defect
from the identity. -/
theorem norm_polarCorrect_sub_le
    (C : Matrix Y Y ℂ) (hP : (cornerGram C).IsHermitian) {delta : ℝ}
    (hC : ‖C‖ ≤ 1) (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram C - 1‖ ≤ delta) :
    ‖polarCorrect C hP - C‖ ≤ 2 * delta := by
  calc
    ‖polarCorrect C hP - C‖ ≤ ‖C‖ * (2 * delta) :=
      norm_polarCorrect_sub_le_mul C hP hdelta hdeltaHalf hclose
    _ ≤ 1 * (2 * delta) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = 2 * delta := one_mul _

/-- The bundled exact unitary supplied by polar correction under a `1/2`
Gram-defect bound. -/
noncomputable def polarCorrectUnitary
    (C : Matrix Y Y ℂ) (hP : (cornerGram C).IsHermitian) {delta : ℝ}
    (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram C - 1‖ ≤ delta) : Matrix.unitaryGroup Y ℂ :=
  ⟨polarCorrect C hP, polarCorrect_mem_unitaryGroup C hP
    (cornerGram_eigenvalues_pos_of_norm_sub_one_le C hP hdeltaHalf hclose)⟩

end KazhdanCornerMatrices
end GroupApproximation
