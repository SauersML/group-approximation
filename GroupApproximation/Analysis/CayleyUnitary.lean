import GroupApproximation.Analysis.OperatorNormCertificate
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Cayley transform of a Hermitian matrix

The arithmetical route to MF recognition needs a countable supply of exactly
unitary matrices that is dense in the unitary group.  The Cayley transform
supplies one: it turns an arbitrary Hermitian matrix into a unitary, and
rational Hermitian matrices are dense in the Hermitian matrices for the trivial
reason that the rationals are dense in the reals.

The transform is written here as

    cayley H = 2 • (1 + I • H)⁻¹ - 1,

which is the usual `(1 - iH)(1 + iH)⁻¹` after the substitution
`1 - iH = 2 - (1 + iH)`.  Two things become easy in this form.

* **Unitarity is pure algebra.**  With `A = 1 + I • H` and `B = star A`, one has
  `A * B = B * A = 1 + H * H` and `A + B = 2`, whence
  `A⁻¹ + B⁻¹ = 2 * (A * B)⁻¹`, and the product `(2B⁻¹ - 1)(2A⁻¹ - 1)` collapses
  to `1`.  No norms and no spectral theory enter.
* **The resolvent is a contraction, for free.**  `‖2 • A⁻¹ - 1‖ = 1` because the
  Cayley transform is unitary, so `‖A⁻¹‖ ≤ 1` by the triangle inequality.  This
  is the estimate that makes the transform Lipschitz with constant `2`.

The one analytic input is invertibility of `1 + Hᴴ * H`, and that is proved by a
kernel argument on the quadratic form, using `dotProduct` directly rather than
the inner-product space structure.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CayleyUnitary

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The quadratic form -/

omit [DecidableEq n] in
/-- The quadratic form is nonnegative. -/
theorem star_dotProduct_self_nonneg (v : n → ℂ) : 0 ≤ (star v ⬝ᵥ v).re := by
  rw [dotProduct]
  simp only [Complex.re_sum, Pi.star_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im]

omit [DecidableEq n] in
/-- The quadratic form vanishes only at zero. -/
theorem eq_zero_of_star_dotProduct_self (v : n → ℂ) (h : (star v ⬝ᵥ v).re = 0) :
    v = 0 := by
  have hterm : ∀ i : n, ((star v i) * v i).re = (v i).re ^ 2 + (v i).im ^ 2 := by
    intro i
    rw [Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  have hsum : ∑ i, ((v i).re ^ 2 + (v i).im ^ 2) = 0 := by
    rw [← h, dotProduct]
    simp only [Complex.re_sum]
    exact (Finset.sum_congr rfl fun i _ => (hterm i).symm)
  have hzero : ∀ i : n, (v i).re ^ 2 + (v i).im ^ 2 = 0 := by
    intro i
    have hnn : ∀ j : n, j ∈ (Finset.univ : Finset n) →
        0 ≤ (v j).re ^ 2 + (v j).im ^ 2 := fun j _ => by positivity
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ i)
  funext i
  have hi := hzero i
  have hre : (v i).re = 0 := by nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im]
  have him : (v i).im = 0 := by nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im]
  exact Complex.ext hre him

omit [DecidableEq n] in
/-- Moving a conjugate transpose across the quadratic form. -/
theorem star_dotProduct_conjTranspose (M : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (Mᴴ *ᵥ (M *ᵥ x)) = star (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/-! ## `1 + Mᴴ * M` is invertible -/

/-- The kernel of `1 + Mᴴ * M` is trivial. -/
theorem eq_zero_of_one_add_conjTranspose_mul_mulVec_eq_zero (M : Matrix n n ℂ)
    (x : n → ℂ) (hx : (1 + Mᴴ * M) *ᵥ x = 0) : x = 0 := by
  have hexp : (1 + Mᴴ * M) *ᵥ x = x + Mᴴ *ᵥ (M *ᵥ x) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  rw [hexp] at hx
  have hx' : Mᴴ *ᵥ (M *ᵥ x) = -x := by
    have := congrArg (fun y => y - x) hx
    simpa using this
  have hq : star x ⬝ᵥ (Mᴴ *ᵥ (M *ᵥ x)) = -(star x ⬝ᵥ x) := by
    rw [hx', dotProduct_neg]
  rw [star_dotProduct_conjTranspose] at hq
  have hre : (star (M *ᵥ x) ⬝ᵥ (M *ᵥ x)).re = -((star x ⬝ᵥ x).re) := by
    rw [hq, Complex.neg_re]
  have h1 := star_dotProduct_self_nonneg (M *ᵥ x)
  have h2 := star_dotProduct_self_nonneg x
  have hzero : (star x ⬝ᵥ x).re = 0 := by linarith
  exact eq_zero_of_star_dotProduct_self x hzero

/-- `1 + Mᴴ * M` has a unit determinant. -/
theorem isUnit_det_one_add_conjTranspose_mul (M : Matrix n n ℂ) :
    IsUnit (1 + Mᴴ * M).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact hv (eq_zero_of_one_add_conjTranspose_mul_mulVec_eq_zero M v hzero)

/-! ## The transform -/

/-- The Cayley denominator `1 + I • H`. -/
def denom (H : Matrix n n ℂ) : Matrix n n ℂ := 1 + Complex.I • H

theorem star_denom {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    star (denom H) = 1 - Complex.I • H := by
  have hstarH : star H = H := by rw [Matrix.star_eq_conjTranspose]; exact hH
  have hI : star (Complex.I) = -Complex.I := by simp
  rw [denom, star_add, star_one, star_smul, hstarH, hI, neg_smul]
  abel

theorem denom_add_star {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    denom H + star (denom H) = 1 + 1 := by
  rw [star_denom hH, denom]
  abel

theorem denom_mul_star {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    denom H * star (denom H) = 1 + H * H := by
  have hsq : (Complex.I • H) * (Complex.I • H) = -(H * H) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul]
  rw [star_denom hH, denom]
  set X : Matrix n n ℂ := Complex.I • H with hX
  have hexp : ((1 : Matrix n n ℂ) + X) * (1 - X) = 1 - X * X := by
    noncomm_ring
  rw [hexp, hsq, sub_neg_eq_add]

theorem star_mul_denom {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    star (denom H) * denom H = 1 + H * H := by
  have hsq : (Complex.I • H) * (Complex.I • H) = -(H * H) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul]
  rw [star_denom hH, denom]
  set X : Matrix n n ℂ := Complex.I • H with hX
  have hexp : ((1 : Matrix n n ℂ) - X) * (1 + X) = 1 - X * X := by
    noncomm_ring
  rw [hexp, hsq, sub_neg_eq_add]

theorem isUnit_det_one_add_self_mul {H : Matrix n n ℂ}
    (hH : Matrix.IsHermitian H) : IsUnit (1 + H * H).det := by
  have h := isUnit_det_one_add_conjTranspose_mul H
  rwa [show (Hᴴ : Matrix n n ℂ) = H from hH] at h

theorem isUnit_det_denom {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    IsUnit (denom H).det := by
  have hprod : (denom H).det * (star (denom H)).det = (1 + H * H).det := by
    rw [← Matrix.det_mul, denom_mul_star hH]
  refine isUnit_of_mul_isUnit_left (y := (star (denom H)).det) ?_
  rw [hprod]
  exact isUnit_det_one_add_self_mul hH

theorem isUnit_det_star_denom {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    IsUnit (star (denom H)).det := by
  have hprod : (star (denom H)).det * (denom H).det = (1 + H * H).det := by
    rw [← Matrix.det_mul, star_mul_denom hH]
  refine isUnit_of_mul_isUnit_left (y := (denom H).det) ?_
  rw [hprod]
  exact isUnit_det_one_add_self_mul hH

/-- **The Cayley transform.** -/
noncomputable def cayley (H : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ) • (denom H)⁻¹ - 1

/-- The sum of the two resolvents. -/
theorem inv_add_inv {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    (denom H)⁻¹ + (star (denom H))⁻¹
      = (2 : ℂ) • ((star (denom H))⁻¹ * (denom H)⁻¹) := by
  have hA := isUnit_det_denom hH
  have hB := isUnit_det_star_denom hH
  have hexpand : (star (denom H))⁻¹ * (star (denom H) + denom H) * (denom H)⁻¹
      = (denom H)⁻¹ + (star (denom H))⁻¹ := by
    rw [mul_add, add_mul, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
  rw [← hexpand, add_comm (star (denom H)) (denom H), denom_add_star hH]
  have htwo : ((1 : Matrix n n ℂ) + 1) = (2 : ℂ) • (1 : Matrix n n ℂ) :=
    (two_smul ℂ (1 : Matrix n n ℂ)).symm
  rw [htwo, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **The Cayley transform is unitary.** -/
theorem cayley_mem_unitaryGroup {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    cayley H ∈ Matrix.unitaryGroup n ℂ := by
  have hA := isUnit_det_denom hH
  have hB := isUnit_det_star_denom hH
  have hstarinv : star ((denom H)⁻¹) = (star (denom H))⁻¹ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_nonsing_inv]
  have hstarC : star (cayley H) = (2 : ℂ) • (star (denom H))⁻¹ - 1 := by
    rw [cayley, star_sub, star_one, star_smul, hstarinv,
      show star ((2 : ℂ)) = (2 : ℂ) by simp]
  have hkey : star (cayley H) * cayley H = 1 := by
    have hsum := inv_add_inv hH
    rw [hstarC, cayley]
    have hexpand :
        ((2 : ℂ) • (star (denom H))⁻¹ - 1) * ((2 : ℂ) • (denom H)⁻¹ - 1)
          = ((2 : ℂ) * 2) • ((star (denom H))⁻¹ * (denom H)⁻¹)
            - (2 : ℂ) • (star (denom H))⁻¹ - (2 : ℂ) • (denom H)⁻¹ + 1 := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      simp only [mul_one]
      abel
    rw [hexpand]
    have h4 : ((2 : ℂ) * 2) • ((star (denom H))⁻¹ * (denom H)⁻¹)
        = (2 : ℂ) • (denom H)⁻¹ + (2 : ℂ) • (star (denom H))⁻¹ := by
      rw [← smul_smul, ← hsum, smul_add]
    rw [h4]
    abel
  refine Matrix.mem_unitaryGroup_iff'.2 ?_
  exact hkey

/-! ## Norm estimates -/

/-- The identity is a contraction. -/
theorem norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [map_one]
  simp

/-- A unitary is a contraction. -/
theorem norm_le_one_of_mem_unitaryGroup {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have hstar : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hsq : ‖U‖ * ‖U‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hstar]
    exact norm_one_le
  nlinarith [norm_nonneg U]

/-- **The Cayley resolvent is a contraction.**  This is where unitarity pays:
the bound needs no spectral information. -/
theorem norm_inv_denom_le {H : Matrix n n ℂ} (hH : Matrix.IsHermitian H) :
    ‖(denom H)⁻¹‖ ≤ 1 := by
  have hsplit : (2 : ℂ) • (denom H)⁻¹ = cayley H + 1 := by
    rw [cayley]; abel
  have hnorm : ‖(2 : ℂ) • (denom H)⁻¹‖ ≤ 2 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_le_one_of_mem_unitaryGroup (cayley_mem_unitaryGroup hH)
    have h2 := norm_one_le (n := n)
    linarith
  rw [norm_smul] at hnorm
  have htwo : ‖(2 : ℂ)‖ = 2 := by simp
  rw [htwo] at hnorm
  linarith

omit [Fintype n] in
/-- The difference of two Cayley denominators. -/
theorem denom_sub_denom (H H' : Matrix n n ℂ) :
    denom H' - denom H = Complex.I • (H' - H) := by
  rw [denom, denom, smul_sub]
  abel

/-- **The Cayley transform is Lipschitz with constant two.** -/
theorem norm_cayley_sub_cayley {H H' : Matrix n n ℂ}
    (hH : Matrix.IsHermitian H) (hH' : Matrix.IsHermitian H') :
    ‖cayley H - cayley H'‖ ≤ 2 * ‖H - H'‖ := by
  have hA := isUnit_det_denom hH
  have hA' := isUnit_det_denom hH'
  have hres : (denom H)⁻¹ - (denom H')⁻¹
      = (denom H)⁻¹ * (denom H' - denom H) * (denom H')⁻¹ := by
    have h1 : (denom H)⁻¹ * denom H' * (denom H')⁻¹ = (denom H)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA', Matrix.mul_one]
    have h2 : (denom H)⁻¹ * denom H * (denom H')⁻¹ = (denom H')⁻¹ := by
      rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    rw [mul_sub, sub_mul, h1, h2]
  have hdiff : cayley H - cayley H'
      = (2 : ℂ) • ((denom H)⁻¹ - (denom H')⁻¹) := by
    rw [cayley, cayley, smul_sub]
    abel
  rw [hdiff, norm_smul, show ‖(2 : ℂ)‖ = 2 by simp, hres, denom_sub_denom]
  have hstep : ‖(denom H)⁻¹ * (Complex.I • (H' - H)) * (denom H')⁻¹‖
      ≤ ‖H - H'‖ := by
    have h1 := Matrix.l2_opNorm_mul ((denom H)⁻¹ * (Complex.I • (H' - H)))
      ((denom H')⁻¹)
    have h2 := Matrix.l2_opNorm_mul ((denom H)⁻¹) (Complex.I • (H' - H))
    have hI : ‖Complex.I • (H' - H)‖ = ‖H' - H‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have hsym : ‖H' - H‖ = ‖H - H'‖ := norm_sub_rev _ _
    have hb1 := norm_inv_denom_le hH
    have hb2 := norm_inv_denom_le hH'
    have hnn : 0 ≤ ‖H' - H‖ := norm_nonneg _
    rw [hI] at h2
    nlinarith [norm_nonneg ((denom H)⁻¹ * (Complex.I • (H' - H))),
      norm_nonneg ((denom H)⁻¹), norm_nonneg ((denom H')⁻¹)]
  linarith

/-! ## Surjectivity

The image of `cayley` is exactly the unitaries `U` for which `1 + U` is
invertible: solving `2 • A⁻¹ - 1 = U` for `A` gives `A = 2 • (1 + U)⁻¹`, and the
Hermitian parameter is read off from `A = 1 + I • H`. -/

/-- For a unitary the conjugate transpose is the inverse. -/
theorem conjTranspose_eq_inv {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ = U⁻¹ := by
  have h : U * Uᴴ = 1 := by
    have h' := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose] at h'
  exact (Matrix.inv_eq_right_inv h).symm

theorem isUnit_det_of_mem_unitaryGroup {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : IsUnit U.det := by
  have h : U * Uᴴ = 1 := by
    have h' := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose] at h'
  refine isUnit_iff_exists_inv.2 ⟨(Uᴴ).det, ?_⟩
  rw [← Matrix.det_mul, h, Matrix.det_one]

/-- The inverse of `1 + U⁻¹`, for an invertible `U` with `1 + U` invertible. -/
theorem inv_one_add_inv {U : Matrix n n ℂ} (hUdet : IsUnit U.det)
    (hinv : IsUnit ((1 : Matrix n n ℂ) + U).det) :
    ((1 : Matrix n n ℂ) + U⁻¹)⁻¹ = (1 + U)⁻¹ * U := by
  refine Matrix.inv_eq_right_inv ?_
  have hfac : (1 : Matrix n n ℂ) + U⁻¹ = U⁻¹ * (1 + U) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.nonsing_inv_mul _ hUdet]
    abel
  rw [hfac, Matrix.mul_assoc, ← Matrix.mul_assoc ((1 : Matrix n n ℂ) + U),
    Matrix.mul_nonsing_inv _ hinv, Matrix.one_mul,
    Matrix.nonsing_inv_mul _ hUdet]

/-- The two resolvents of `1 + U` add to one. -/
theorem inv_mul_add_inv {U : Matrix n n ℂ}
    (hinv : IsUnit ((1 : Matrix n n ℂ) + U).det) :
    (1 + U)⁻¹ * U + (1 + U)⁻¹ = 1 := by
  have hstep : ((1 : Matrix n n ℂ) + U)⁻¹ * U + (1 + U)⁻¹
      = (1 + U)⁻¹ * (1 + U) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    abel
  rw [hstep, Matrix.nonsing_inv_mul _ hinv]

/-- The Hermitian parameter of a unitary without eigenvalue `-1`. -/
noncomputable def param (U : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • ((2 : ℂ) • (1 + U)⁻¹ - 1)

/-- The bracket is anti-Hermitian. -/
theorem star_bracket {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hinv : IsUnit ((1 : Matrix n n ℂ) + U).det) :
    star ((2 : ℂ) • (1 + U)⁻¹ - 1) = -((2 : ℂ) • (1 + U)⁻¹ - 1) := by
  have hUdet := isUnit_det_of_mem_unitaryGroup hU
  have hUinv : star U = U⁻¹ := by
    rw [Matrix.star_eq_conjTranspose]; exact conjTranspose_eq_inv hU
  have hstarinv : star (((1 : Matrix n n ℂ) + U)⁻¹) = (star (1 + U))⁻¹ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_nonsing_inv]
  have hs1U : star ((1 : Matrix n n ℂ) + U) = 1 + U⁻¹ := by
    rw [star_add, star_one, hUinv]
  rw [star_sub, star_one, star_smul, hstarinv, hs1U,
    inv_one_add_inv hUdet hinv, show star ((2 : ℂ)) = (2 : ℂ) by simp]
  have hsum := inv_mul_add_inv hinv
  have h2 : (2 : ℂ) • (((1 : Matrix n n ℂ) + U)⁻¹ * U)
      + (2 : ℂ) • ((1 : Matrix n n ℂ) + U)⁻¹ = 1 + 1 := by
    rw [← smul_add, hsum]
    exact two_smul ℂ (1 : Matrix n n ℂ)
  refine sub_eq_zero.1 ?_
  have hrewrite : (2 : ℂ) • (((1 : Matrix n n ℂ) + U)⁻¹ * U) - 1
        - -((2 : ℂ) • ((1 : Matrix n n ℂ) + U)⁻¹ - 1)
      = ((2 : ℂ) • (((1 : Matrix n n ℂ) + U)⁻¹ * U)
          + (2 : ℂ) • ((1 : Matrix n n ℂ) + U)⁻¹) - (1 + 1) := by abel
  rw [hrewrite, h2, sub_self]

theorem isHermitian_param {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hinv : IsUnit ((1 : Matrix n n ℂ) + U).det) :
    Matrix.IsHermitian (param U) := by
  have hstar : star (param U) = param U := by
    rw [param, star_smul, star_bracket hU hinv,
      show star (-Complex.I) = Complex.I by simp, smul_neg, ← neg_smul]
  rw [Matrix.star_eq_conjTranspose] at hstar
  exact hstar

theorem denom_param {U : Matrix n n ℂ} :
    denom (param U) = (2 : ℂ) • ((1 : Matrix n n ℂ) + U)⁻¹ := by
  have hI : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [denom, param, smul_smul, hI, one_smul]
  abel

/-- **Every unitary without eigenvalue `-1` is a Cayley transform.** -/
theorem cayley_param {U : Matrix n n ℂ}
    (hinv : IsUnit ((1 : Matrix n n ℂ) + U).det) :
    cayley (param U) = U := by
  have hres : (denom (param U))⁻¹ = ((1 : ℂ) / 2) • ((1 : Matrix n n ℂ) + U) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [denom_param, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.nonsing_inv_mul _ hinv]
    norm_num
  rw [cayley, hres, smul_smul]
  norm_num

end CayleyUnitary
end GroupApproximation
