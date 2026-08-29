import GroupApproximation.Sofic.KazhdanCornerModel

/-!
# The equal-rank projection flip

The finite-dimensional replacement for stable finiteness of a matrix corona.
If two orthogonal projection matrices have equal rank and the first is almost
contained in the range of the second, then the second is almost contained in
the range of the first, with an explicit operator-norm constant.  The proof is
a dimension count: compression by the second projection is injective on the
range of the first, hence surjective onto the range of the second, and unit
vectors there pull back with controlled norm.

This one-sided-to-two-sided upgrade is exactly what the operator-norm
Kazhdan-compressor argument needs; the normalized-trace comparison of the two
projections is strictly weaker and does not suffice downstream.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y]

/-! ## Generic quadratic-form bridges -/

/-- The entrywise squared Euclidean norm of a matrix–vector product is the
real part of the Gram quadratic form, for an arbitrary finite coordinate
type. -/
theorem sum_normSq_mulVec_eq_re_gram_general (X : Matrix Y Y ℂ) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((X *ᵥ x) i) =
      (star x ⬝ᵥ ((Xᴴ * X) *ᵥ x)).re := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  change (∑ i : Y, Complex.normSq ((X *ᵥ x) i)) =
    (∑ i : Y, star ((X *ᵥ x) i) * (X *ᵥ x) i).re
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let z := (X *ᵥ x) i
  calc
    Complex.normSq z = ((Complex.normSq z : ℝ) : ℂ).re := by simp
    _ = (star z * z).re :=
      congrArg Complex.re Complex.normSq_eq_conj_mul_self

section Decidable

variable [DecidableEq Y]

/-- The identity-matrix case of the Gram bridge: the quadratic form of `1` is
the squared Euclidean norm. -/
theorem re_dotProduct_self (x : Y → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i : Y, Complex.normSq (x i) := by
  have h := sum_normSq_mulVec_eq_re_gram_general (1 : Matrix Y Y ℂ) x
  simpa using h.symm

/-- Orthogonal splitting of the squared Euclidean norm along an orthogonal
projection matrix. -/
theorem sum_normSq_proj_split {r : Matrix Y Y ℂ}
    (hr : IsOrthogonalProjectionMatrix r) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((r *ᵥ x) i) +
      ∑ i : Y, Complex.normSq (((1 - r) *ᵥ x) i) =
      ∑ i : Y, Complex.normSq (x i) := by
  have hr' : rᴴ * r = r := by rw [hr.1, hr.2]
  have hc := one_sub_isOrthogonalProjection hr
  have hc' : (1 - r)ᴴ * (1 - r) = 1 - r := by rw [hc.1, hc.2]
  rw [sum_normSq_mulVec_eq_re_gram_general, sum_normSq_mulVec_eq_re_gram_general,
    hr', hc', ← re_dotProduct_self]
  calc
    (star x ⬝ᵥ (r *ᵥ x)).re + (star x ⬝ᵥ ((1 - r) *ᵥ x)).re =
        (star x ⬝ᵥ (r *ᵥ x + (1 - r) *ᵥ x)).re := by
      rw [dotProduct_add, Complex.add_re]
    _ = (star x ⬝ᵥ x).re := by rw [← Matrix.add_mulVec]; simp

/-- An orthogonal projection matrix contracts squared Euclidean norms. -/
theorem sum_normSq_mulVec_proj_le {r : Matrix Y Y ℂ}
    (hr : IsOrthogonalProjectionMatrix r) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((r *ᵥ x) i) ≤ ∑ i : Y, Complex.normSq (x i) := by
  have h := sum_normSq_proj_split hr x
  have hnn : 0 ≤ ∑ i : Y, Complex.normSq (((1 - r) *ᵥ x) i) :=
    Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
  linarith only [h, hnn]

/-- Squared-norm preservation under a matrix with orthonormal columns. -/
theorem sum_normSq_mulVec_of_star_mul_self {U : Matrix Y Y ℂ}
    (hU : Uᴴ * U = 1) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((U *ᵥ x) i) = ∑ i : Y, Complex.normSq (x i) := by
  rw [sum_normSq_mulVec_eq_re_gram_general, hU]
  simpa using re_dotProduct_self x

end Decidable

/-! ## Range membership -/

/-- Vectors in the range of an orthogonal projection matrix are fixed by it.
-/
theorem mulVec_eq_self_of_mem_range {p : Matrix Y Y ℂ}
    (hp : IsOrthogonalProjectionMatrix p) {x : Y → ℂ}
    (hx : x ∈ LinearMap.range p.mulVecLin) : p *ᵥ x = x := by
  obtain ⟨u, rfl⟩ := hx
  show p *ᵥ (p *ᵥ u) = p *ᵥ u
  rw [Matrix.mulVec_mulVec, hp.2]

section Decidable

variable [DecidableEq Y]

/-- For a vector in the range of `p`, the compression by `q` loses at most the
leakage `‖(1 - q) * p‖`. -/
theorem sum_normSq_compress_ge {p q : Matrix Y Y ℂ}
    (hp : IsOrthogonalProjectionMatrix p) (hq : IsOrthogonalProjectionMatrix q)
    {ε : ℝ} (hleak : ‖(1 - q) * p‖ ≤ ε) (hε0 : 0 ≤ ε)
    {x : Y → ℂ} (hx : x ∈ LinearMap.range p.mulVecLin) :
    (1 - ε ^ 2) * ∑ i : Y, Complex.normSq (x i) ≤
      ∑ i : Y, Complex.normSq ((q *ᵥ x) i) := by
  have hfix : p *ᵥ x = x := mulVec_eq_self_of_mem_range hp hx
  have hcompl : (1 - q) *ᵥ x = ((1 - q) * p) *ᵥ x := by
    rw [← Matrix.mulVec_mulVec, hfix]
  have hbound : ∑ i : Y, Complex.normSq (((1 - q) *ᵥ x) i) ≤
      ε ^ 2 * ∑ i : Y, Complex.normSq (x i) := by
    rw [hcompl]
    calc
      ∑ i : Y, Complex.normSq ((((1 - q) * p) *ᵥ x) i) ≤
          ‖(1 - q) * p‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) :=
        sum_normSq_mulVec_le_general _ x
      _ ≤ ε ^ 2 * ∑ i : Y, Complex.normSq (x i) := by
        have hsq : ‖(1 - q) * p‖ ^ 2 ≤ ε ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hε0).2 hleak
        exact mul_le_mul_of_nonneg_right hsq
          (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
  have hsplit := sum_normSq_proj_split hq x
  nlinarith only [hbound, hsplit, Finset.sum_nonneg
    (fun i (_ : i ∈ Finset.univ) ↦ Complex.normSq_nonneg (x i))]

/-! ## The flip -/

/-- **Equal-rank projection flip.**  If two orthogonal projection matrices
have the same rank and `‖(1 - q) * p‖ ≤ ε < 1`, then
`‖(1 - p) * q‖ ≤ ε / √(1 - ε²)`.

This is the operator-norm form of finite-dimensional stable finiteness: a
projection unitarily equivalent to an almost-subprojection is almost equal to
it. -/
theorem norm_one_sub_mul_flip {p q : Matrix Y Y ℂ}
    (hp : IsOrthogonalProjectionMatrix p) (hq : IsOrthogonalProjectionMatrix q)
    (hrank : p.rank = q.rank) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hleak : ‖(1 - q) * p‖ ≤ ε) :
    ‖(1 - p) * q‖ ≤ ε / Real.sqrt (1 - ε ^ 2) := by
  classical
  have hden : (0 : ℝ) < 1 - ε ^ 2 := by
    nlinarith only [hε0, hε1]
  have hc0 : 0 ≤ ε / Real.sqrt (1 - ε ^ 2) :=
    div_nonneg hε0 (Real.sqrt_nonneg _)
  -- the compression map between the two ranges
  let f : LinearMap.range p.mulVecLin →ₗ[ℂ] LinearMap.range q.mulVecLin :=
    LinearMap.codRestrict _ (q.mulVecLin.comp (LinearMap.range p.mulVecLin).subtype)
      (fun x ↦ LinearMap.mem_range_self _ _)
  have hf_apply : ∀ x : LinearMap.range p.mulVecLin,
      (f x : Y → ℂ) = q *ᵥ (x : Y → ℂ) := fun x ↦ rfl
  -- injectivity from the leakage bound
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have hzero : q *ᵥ (x : Y → ℂ) = 0 := by
      have := congrArg (Subtype.val) (LinearMap.mem_ker.mp hx)
      simpa [hf_apply] using this
    have hlow := sum_normSq_compress_ge hp hq hleak hε0 x.2
    rw [hzero] at hlow
    simp only [Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero] at hlow
    have hxzero : ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) = 0 := by
      have hnn : 0 ≤ ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) :=
        Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
      nlinarith only [hlow, hnn, hden]
    have hxz : (x : Y → ℂ) = 0 := by
      funext i
      have hi : Complex.normSq ((x : Y → ℂ) i) = 0 := by
        have hmem :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun i (_ : i ∈ Finset.univ) ↦ Complex.normSq_nonneg
              ((x : Y → ℂ) i))).mp hxzero i (Finset.mem_univ i)
        exact hmem
      exact Complex.normSq_eq_zero.mp hi
    exact Subtype.ext hxz
  -- equal ranks force surjectivity
  have hfr : Module.finrank ℂ (LinearMap.range p.mulVecLin) =
      Module.finrank ℂ (LinearMap.range q.mulVecLin) := hrank
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hf_inj
  -- the pointwise bound on the range of q
  have hrangebound : ∀ y : Y → ℂ, y ∈ LinearMap.range q.mulVecLin →
      ∑ i : Y, Complex.normSq (((1 - p) *ᵥ y) i) ≤
        ε ^ 2 / (1 - ε ^ 2) * ∑ i : Y, Complex.normSq (y i) := by
    intro y hy
    obtain ⟨x, hxy⟩ := hf_surj ⟨y, hy⟩
    have hqx : q *ᵥ (x : Y → ℂ) = y := by
      have := congrArg Subtype.val hxy
      simpa [hf_apply] using this
    -- norm control on the preimage
    have hxbound : ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) ≤
        (1 - ε ^ 2)⁻¹ * ∑ i : Y, Complex.normSq (y i) := by
      have hlow := sum_normSq_compress_ge hp hq hleak hε0 x.2
      rw [hqx] at hlow
      rw [le_inv_mul_iff₀ hden]
      exact hlow
    -- the compression error vector
    have hfix : p *ᵥ (x : Y → ℂ) = (x : Y → ℂ) :=
      mulVec_eq_self_of_mem_range hp x.2
    have hyerr : (1 - p) *ᵥ y = (1 - p) *ᵥ (((q - 1) * p) *ᵥ (x : Y → ℂ)) := by
      have h1 : (1 - p) *ᵥ y = (1 - p) *ᵥ (q *ᵥ (x : Y → ℂ)) := by rw [hqx]
      have h2 : q *ᵥ (x : Y → ℂ) =
          (q - 1) *ᵥ (x : Y → ℂ) + (x : Y → ℂ) := by
        rw [Matrix.sub_mulVec]
        simp
      have h3 : (1 - p) *ᵥ (x : Y → ℂ) = 0 := by
        rw [Matrix.sub_mulVec, hfix]
        simp
      have h4 : (q - 1) *ᵥ (x : Y → ℂ) = ((q - 1) * p) *ᵥ (x : Y → ℂ) := by
        rw [← Matrix.mulVec_mulVec, hfix]
      rw [h1, h2, Matrix.mulVec_add, h3, add_zero, h4]
    have hnormfactor : ‖(q - 1) * p‖ ≤ ε := by
      have hneg : (q - 1) * p = -((1 - q) * p) := by noncomm_ring
      rw [hneg, norm_neg]
      exact hleak
    have hprojContract :
        ∑ i : Y, Complex.normSq
            (((1 - p) *ᵥ (((q - 1) * p) *ᵥ (x : Y → ℂ))) i) ≤
          ∑ i : Y, Complex.normSq ((((q - 1) * p) *ᵥ (x : Y → ℂ)) i) :=
      sum_normSq_mulVec_proj_le (one_sub_isOrthogonalProjection hp)
        (((q - 1) * p) *ᵥ (x : Y → ℂ))
    calc
      ∑ i : Y, Complex.normSq (((1 - p) *ᵥ y) i) =
          ∑ i : Y, Complex.normSq
            (((1 - p) *ᵥ (((q - 1) * p) *ᵥ (x : Y → ℂ))) i) := by rw [hyerr]
      _ ≤ ∑ i : Y, Complex.normSq ((((q - 1) * p) *ᵥ (x : Y → ℂ)) i) :=
        hprojContract
      _ ≤ ‖(q - 1) * p‖ ^ 2 * ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) :=
        sum_normSq_mulVec_le_general _ _
      _ ≤ ε ^ 2 * ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) := by
        have hsq : ‖(q - 1) * p‖ ^ 2 ≤ ε ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hε0).2 hnormfactor
        exact mul_le_mul_of_nonneg_right hsq
          (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
      _ ≤ ε ^ 2 * ((1 - ε ^ 2)⁻¹ * ∑ i : Y, Complex.normSq (y i)) :=
        mul_le_mul_of_nonneg_left hxbound (by positivity)
      _ = ε ^ 2 / (1 - ε ^ 2) * ∑ i : Y, Complex.normSq (y i) := by
        rw [div_eq_mul_inv]
        ring
  -- conclude the operator-norm bound
  refine l2_opNorm_le_of_sum_normSq_general _ hc0 fun v ↦ ?_
  have hcsq : (ε / Real.sqrt (1 - ε ^ 2)) ^ 2 = ε ^ 2 / (1 - ε ^ 2) := by
    rw [div_pow, Real.sq_sqrt hden.le]
  rw [hcsq]
  have hmem : q *ᵥ v ∈ LinearMap.range q.mulVecLin :=
    LinearMap.mem_range_self _ v
  have hstep := hrangebound (q *ᵥ v) hmem
  have hcontract : ∑ i : Y, Complex.normSq ((q *ᵥ v) i) ≤
      ∑ i : Y, Complex.normSq (v i) := sum_normSq_mulVec_proj_le hq v
  have hassoc : ((1 - p) * q) *ᵥ v = (1 - p) *ᵥ (q *ᵥ v) :=
    (Matrix.mulVec_mulVec _ _ _).symm
  rw [hassoc]
  calc
    ∑ i : Y, Complex.normSq (((1 - p) *ᵥ (q *ᵥ v)) i) ≤
        ε ^ 2 / (1 - ε ^ 2) * ∑ i : Y, Complex.normSq ((q *ᵥ v) i) := hstep
    _ ≤ ε ^ 2 / (1 - ε ^ 2) * ∑ i : Y, Complex.normSq (v i) :=
      mul_le_mul_of_nonneg_left hcontract (by positivity)

/-! ## Companions -/

/-- Unitary determinants are units. -/
theorem isUnit_det_of_mem_unitaryGroup {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) : IsUnit u.det := by
  have hmul : u * uᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have hdet : u.det * uᴴ.det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [isUnit_iff_ne_zero]
  intro hzero
  rw [hzero, zero_mul] at hdet
  exact zero_ne_one hdet

/-- Exact unitary conjugation preserves matrix rank. -/
theorem rank_unitary_conj {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) (p : Matrix Y Y ℂ) :
    (u * p * uᴴ).rank = p.rank := by
  have hustar : uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hu
  have hdet_u : IsUnit u.det := isUnit_det_of_mem_unitaryGroup hu
  have hdet_ustar : IsUnit uᴴ.det := isUnit_det_of_mem_unitaryGroup hustar
  calc
    (u * p * uᴴ).rank = (u * p).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det uᴴ (u * p) hdet_ustar
    _ = p.rank := Matrix.rank_mul_eq_right_of_isUnit_det u p hdet_u

end Decidable

end KazhdanCornerMatrices
end GroupApproximation
