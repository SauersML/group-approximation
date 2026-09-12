import GroupApproximation.Sofic.ProjectionRankFlip

/-!
# Spectral capture below a threshold

A vector (or contraction) almost fixed by an almost-contractive Hermitian
matrix is almost supported on the spectral subspace above any threshold below
one.  The estimate is the one-line eigenbasis inequality
`(1 - t)·1_{λ ≤ t} ≤ (1 - λ) + δ` for `λ ≤ 1 + δ`, integrated against the
squared eigencoordinates; Cauchy–Schwarz converts the quadratic form of
`1 - H` into the displacement norm.

Both a vector form and an operator form are provided; the operator form is
the one consumed by the Kazhdan-compressor order argument, the vector form by
the lamp-vector step.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## Dot-product bridges -/

/-- Isometries of the dot product from orthonormal columns. -/
theorem star_mulVec_dotProduct_mulVec {U : Matrix Y Y ℂ}
    (hU : Uᴴ * U = 1) (w v : Y → ℂ) :
    star (U *ᵥ w) ⬝ᵥ (U *ᵥ v) = star w ⬝ᵥ v := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hU, Matrix.vecMul_one]

omit [DecidableEq Y] in
/-- Cauchy–Schwarz for the complex dot product, in `normSq`-sum form. -/
theorem re_star_dotProduct_le_sqrt (y z : Y → ℂ) :
    (star y ⬝ᵥ z).re ≤
      Real.sqrt (∑ i : Y, Complex.normSq (y i)) *
        Real.sqrt (∑ i : Y, Complex.normSq (z i)) := by
  let yE : EuclideanSpace ℂ Y := (EuclideanSpace.equiv Y ℂ).symm y
  let zE : EuclideanSpace ℂ Y := (EuclideanSpace.equiv Y ℂ).symm z
  have hinner : (star y ⬝ᵥ z).re = RCLike.re (inner ℂ yE zE) := by
    simp only [yE, zE, EuclideanSpace.inner_eq_star_dotProduct]
    rw [dotProduct_comm]
    rfl
  have hyE : ‖yE‖ = Real.sqrt (∑ i : Y, Complex.normSq (y i)) := by
    rw [← euclidean_norm_sq_general y, Real.sqrt_sq (norm_nonneg _)]
  have hzE : ‖zE‖ = Real.sqrt (∑ i : Y, Complex.normSq (z i)) := by
    rw [← euclidean_norm_sq_general z, Real.sqrt_sq (norm_nonneg _)]
  calc
    (star y ⬝ᵥ z).re = RCLike.re (inner ℂ yE zE) := hinner
    _ ≤ ‖yE‖ * ‖zE‖ := re_inner_le_norm _ _
    _ = Real.sqrt (∑ i : Y, Complex.normSq (y i)) *
        Real.sqrt (∑ i : Y, Complex.normSq (z i)) := by rw [hyE, hzE]

/-! ## The quadratic-form capture bound -/

/-- The core spectral estimate:  the mass of a vector below the spectral
threshold is controlled by the quadratic form of `1 - H`, up to the excess
`δ` of `‖H‖` over `1`. -/
theorem spectralBelow_quadratic_bound {H : Matrix Y Y ℂ}
    (hH : H.IsHermitian) {δ t : ℝ} (hδ : 0 ≤ δ) (hHnorm : ‖H‖ ≤ 1 + δ)
    (y : Y → ℂ) :
    (1 - t) * ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ y) i) ≤
      (star y ⬝ᵥ ((1 - H) *ᵥ y)).re +
        δ * ∑ i : Y, Complex.normSq (y i) := by
  classical
  let U : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let L : Matrix Y Y ℂ := Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let D : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then (1 : ℂ) else 0)
  let v : Y → ℂ := Uᴴ *ᵥ y
  have hUU : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hyv : y = U *ᵥ v := by
    show y = U *ᵥ (Uᴴ *ᵥ y)
    rw [Matrix.mulVec_mulVec, hUUstar, Matrix.one_mulVec]
  have hHdiag : H = U * L * Uᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = U * L * Uᴴ := by rfl
  -- the compression in eigencoordinates
  have hSA : spectralAbove H hH t = U * D * Uᴴ := rfl
  have hRconj : U * (1 - D) * Uᴴ = spectralBelow H hH t := by
    show U * (1 - D) * Uᴴ = 1 - spectralAbove H hH t
    rw [hSA, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUUstar]
  have hRy : spectralBelow H hH t *ᵥ y = U *ᵥ ((1 - D) *ᵥ v) := by
    rw [← hRconj]
    show (U * (1 - D) * Uᴴ) *ᵥ y = U *ᵥ ((1 - D) *ᵥ (Uᴴ *ᵥ y))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  -- squared masses in eigencoordinates
  have hNv : ∑ i : Y, Complex.normSq (y i) =
      ∑ i : Y, Complex.normSq (v i) := by
    conv_lhs => rw [hyv]
    exact sum_normSq_mulVec_of_star_mul_self hUU v
  have hNRy : ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ y) i) =
      ∑ i : Y, (if t < hH.eigenvalues i then (0 : ℝ) else 1) *
        Complex.normSq (v i) := by
    rw [hRy, sum_normSq_mulVec_of_star_mul_self hUU]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hentry : ((1 - D) *ᵥ v) i =
        (1 - (if t < hH.eigenvalues i then (1 : ℂ) else 0)) * v i := by
      simp only [D, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
        Matrix.mulVec_diagonal]
      ring
    rw [hentry]
    by_cases hi : t < hH.eigenvalues i
    · simp [hi]
    · simp [hi]
  -- the quadratic form in eigencoordinates
  have h1Hconj : U * (1 - L) * Uᴴ = 1 - H := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUUstar, ← hHdiag]
  have hvec1H : (1 - H) *ᵥ y = U *ᵥ ((1 - L) *ᵥ v) := by
    rw [← h1Hconj]
    show (U * (1 - L) * Uᴴ) *ᵥ y = U *ᵥ ((1 - L) *ᵥ (Uᴴ *ᵥ y))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hgram : (star y ⬝ᵥ ((1 - H) *ᵥ y)).re =
      ∑ i : Y, (1 - hH.eigenvalues i) * Complex.normSq (v i) := by
    have hiso := star_mulVec_dotProduct_mulVec hUU v ((1 - L) *ᵥ v)
    rw [← hyv] at hiso
    rw [hvec1H, hiso]
    simp only [dotProduct, Pi.star_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hentry : ((1 - L) *ᵥ v) i = (1 - (hH.eigenvalues i : ℂ)) * v i := by
      simp only [L, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
        Matrix.mulVec_diagonal]
      ring
    rw [hentry]
    have hrearr : star (v i) * ((1 - (hH.eigenvalues i : ℂ)) * v i) =
        (1 - (hH.eigenvalues i : ℂ)) * (star (v i) * v i) := by ring
    rw [hrearr, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    have hcast : (1 - (hH.eigenvalues i : ℂ)) =
        (((1 - hH.eigenvalues i : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  -- per-eigenvalue comparison
  rw [hNRy, hNv, hgram, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hnn : 0 ≤ Complex.normSq (v i) := Complex.normSq_nonneg _
  by_cases hi : t < hH.eigenvalues i
  · simp only [hi, if_true, zero_mul, mul_zero]
    have hup : hH.eigenvalues i ≤ 1 + δ :=
      le_trans (le_abs_self _)
        ((abs_hermitianEigenvalue_le_norm H hH i).trans hHnorm)
    have hcoef : 0 ≤ 1 - hH.eigenvalues i + δ := by linarith
    nlinarith [mul_nonneg hcoef hnn]
  · simp only [hi, if_false, one_mul]
    have hi' : hH.eigenvalues i ≤ t := not_lt.mp hi
    have hcoef : 1 - t ≤ 1 - hH.eigenvalues i := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hnn, mul_nonneg hδ hnn]

/-! ## The vector form -/

/-- **Vector capture.**  An almost-fixed vector of an almost-contractive
Hermitian matrix is almost supported above every threshold below `1`. -/
theorem spectralBelow_mulVec_capture {H : Matrix Y Y ℂ}
    (hH : H.IsHermitian) {δ t : ℝ} (hδ : 0 ≤ δ) (hHnorm : ‖H‖ ≤ 1 + δ)
    (ξ : Y → ℂ) :
    (1 - t) * ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ ξ) i) ≤
      Real.sqrt (∑ i : Y, Complex.normSq ((ξ - H *ᵥ ξ) i)) *
        Real.sqrt (∑ i : Y, Complex.normSq (ξ i)) +
        δ * ∑ i : Y, Complex.normSq (ξ i) := by
  have hvec : (1 - H) *ᵥ ξ = ξ - H *ᵥ ξ := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hcore := spectralBelow_quadratic_bound hH hδ hHnorm (t := t) ξ
  have hCS : (star ξ ⬝ᵥ ((1 - H) *ᵥ ξ)).re ≤
      Real.sqrt (∑ i : Y, Complex.normSq ((ξ - H *ᵥ ξ) i)) *
        Real.sqrt (∑ i : Y, Complex.normSq (ξ i)) := by
    rw [hvec]
    calc
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
          Real.sqrt (∑ i : Y, Complex.normSq (ξ i)) *
            Real.sqrt (∑ i : Y, Complex.normSq ((ξ - H *ᵥ ξ) i)) :=
        re_star_dotProduct_le_sqrt _ _
      _ = Real.sqrt (∑ i : Y, Complex.normSq ((ξ - H *ᵥ ξ) i)) *
          Real.sqrt (∑ i : Y, Complex.normSq (ξ i)) := mul_comm _ _
  linarith

/-! ## The operator form -/

/-- **Operator capture.**  A contraction almost fixed by an
almost-contractive Hermitian matrix is almost supported above every
threshold below `1`:

`(1 - t) · ‖(1 - P) C‖² ≤ ‖C - H C‖ + δ`  for `P = spectralAbove H t`. -/
theorem norm_spectralBelow_mul_sq_le {H : Matrix Y Y ℂ}
    (hH : H.IsHermitian) {δ t : ℝ} (hδ : 0 ≤ δ) (hHnorm : ‖H‖ ≤ 1 + δ)
    (ht : t < 1) {C : Matrix Y Y ℂ} (hC : ‖C‖ ≤ 1) :
    (1 - t) * ‖spectralBelow H hH t * C‖ ^ 2 ≤ ‖C - H * C‖ + δ := by
  classical
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hnum : (0 : ℝ) ≤ ‖C - H * C‖ + δ := by positivity
  have hpoint : ∀ x : Y → ℂ,
      (1 - t) *
        ∑ i : Y, Complex.normSq (((spectralBelow H hH t * C) *ᵥ x) i) ≤
        (‖C - H * C‖ + δ) * ∑ i : Y, Complex.normSq (x i) := by
    intro x
    set y : Y → ℂ := C *ᵥ x with hydef
    have hassoc : (spectralBelow H hH t * C) *ᵥ x =
        spectralBelow H hH t *ᵥ y := by
      rw [hydef, Matrix.mulVec_mulVec]
    have hNx_nonneg : 0 ≤ ∑ i : Y, Complex.normSq (x i) :=
      Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
    have hNy_le : ∑ i : Y, Complex.normSq (y i) ≤
        ∑ i : Y, Complex.normSq (x i) := by
      rw [hydef]
      calc
        ∑ i : Y, Complex.normSq ((C *ᵥ x) i) ≤
            ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) :=
          sum_normSq_mulVec_le_general C x
        _ ≤ 1 * ∑ i : Y, Complex.normSq (x i) := by
          have h1 : ‖C‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg C]
          exact mul_le_mul_of_nonneg_right h1 hNx_nonneg
        _ = ∑ i : Y, Complex.normSq (x i) := one_mul _
    have hcore := spectralBelow_quadratic_bound hH hδ hHnorm (t := t) y
    -- Cauchy–Schwarz on the quadratic form
    have hvec : (1 - H) *ᵥ y = (C - H * C) *ᵥ x := by
      rw [hydef, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul]
    have hCS : (star y ⬝ᵥ ((1 - H) *ᵥ y)).re ≤
        ‖C - H * C‖ * ∑ i : Y, Complex.normSq (x i) := by
      rw [hvec]
      have hNz_le : ∑ i : Y, Complex.normSq (((C - H * C) *ᵥ x) i) ≤
          ‖C - H * C‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) :=
        sum_normSq_mulVec_le_general _ x
      have hsy : Real.sqrt (∑ i : Y, Complex.normSq (y i)) ≤
          Real.sqrt (∑ i : Y, Complex.normSq (x i)) :=
        Real.sqrt_le_sqrt hNy_le
      have hsz : Real.sqrt
          (∑ i : Y, Complex.normSq (((C - H * C) *ᵥ x) i)) ≤
          ‖C - H * C‖ * Real.sqrt (∑ i : Y, Complex.normSq (x i)) := by
        have hrhs : ‖C - H * C‖ *
            Real.sqrt (∑ i : Y, Complex.normSq (x i)) =
            Real.sqrt (‖C - H * C‖ ^ 2 *
              ∑ i : Y, Complex.normSq (x i)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
        rw [hrhs]
        exact Real.sqrt_le_sqrt hNz_le
      calc
        (star y ⬝ᵥ ((C - H * C) *ᵥ x)).re ≤
            Real.sqrt (∑ i : Y, Complex.normSq (y i)) *
              Real.sqrt (∑ i : Y,
                Complex.normSq (((C - H * C) *ᵥ x) i)) :=
          re_star_dotProduct_le_sqrt _ _
        _ ≤ Real.sqrt (∑ i : Y, Complex.normSq (x i)) *
            (‖C - H * C‖ * Real.sqrt (∑ i : Y, Complex.normSq (x i))) :=
          mul_le_mul hsy hsz (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = ‖C - H * C‖ * (Real.sqrt (∑ i : Y, Complex.normSq (x i)) *
            Real.sqrt (∑ i : Y, Complex.normSq (x i))) := by ring
        _ = ‖C - H * C‖ * ∑ i : Y, Complex.normSq (x i) := by
          rw [Real.mul_self_sqrt hNx_nonneg]
    have hδy : δ * ∑ i : Y, Complex.normSq (y i) ≤
        δ * ∑ i : Y, Complex.normSq (x i) :=
      mul_le_mul_of_nonneg_left hNy_le hδ
    calc
      (1 - t) *
          ∑ i : Y, Complex.normSq (((spectralBelow H hH t * C) *ᵥ x) i) =
          (1 - t) *
            ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ y) i) := by
        rw [hassoc]
      _ ≤ (star y ⬝ᵥ ((1 - H) *ᵥ y)).re +
          δ * ∑ i : Y, Complex.normSq (y i) := hcore
      _ ≤ ‖C - H * C‖ * ∑ i : Y, Complex.normSq (x i) +
          δ * ∑ i : Y, Complex.normSq (x i) := add_le_add hCS hδy
      _ = (‖C - H * C‖ + δ) * ∑ i : Y, Complex.normSq (x i) := by ring
  have hs : (0 : ℝ) ≤ (‖C - H * C‖ + δ) / (1 - t) := by positivity
  have hop : ‖spectralBelow H hH t * C‖ ≤
      Real.sqrt ((‖C - H * C‖ + δ) / (1 - t)) := by
    refine l2_opNorm_le_of_sum_normSq_general _ (Real.sqrt_nonneg _)
      fun x ↦ ?_
    rw [Real.sq_sqrt hs]
    have h := hpoint x
    rw [div_mul_eq_mul_div, le_div_iff₀ h1t]
    calc
      (∑ i : Y, Complex.normSq (((spectralBelow H hH t * C) *ᵥ x) i)) *
          (1 - t) =
          (1 - t) *
            ∑ i : Y, Complex.normSq (((spectralBelow H hH t * C) *ᵥ x) i) := by
        ring
      _ ≤ (‖C - H * C‖ + δ) * ∑ i : Y, Complex.normSq (x i) := h
  have hsq : ‖spectralBelow H hH t * C‖ ^ 2 ≤
      (‖C - H * C‖ + δ) / (1 - t) := by
    have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hop
    rwa [Real.sq_sqrt hs] at h
  calc
    (1 - t) * ‖spectralBelow H hH t * C‖ ^ 2 ≤
        (1 - t) * ((‖C - H * C‖ + δ) / (1 - t)) :=
      mul_le_mul_of_nonneg_left hsq h1t.le
    _ = ‖C - H * C‖ + δ := by field_simp

end KazhdanCornerMatrices
end GroupApproximation
