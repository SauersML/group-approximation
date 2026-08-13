import GroupApproximation.Sofic.KazhdanCornerCompression

/-!
# Dimension-free spectral capture

This file isolates the finite-dimensional estimate which turns a small
`H`-displacement into concentration in the spectral subspace of a Hermitian
matrix above a fixed threshold.  It is deliberately independent of the
group- and approximation-level constructions.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {Y : FiniteModel}

/-- A nonnegative diagonal matrix is positive semidefinite. -/
theorem diagonal_posSemidef_of_nonneg (d : Y → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal fun i ↦ (d i : ℂ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_diagonal fun i ↦ (d i : ℂ)) fun x ↦ ?_
  simp only [Matrix.diagonal_mulVec, dotProduct, starRingEnd_apply,
    map_mul, map_sum]
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun i _ ↦ by
    rw [show star (x i) * ((d i : ℂ) * x i) =
      (d i : ℂ) * (star (x i) * x i) by ring]
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.ofReal_mul_re, Complex.ofReal_re]
    exact mul_nonneg (hd i) (Complex.normSq_nonneg _)

/-- **Spectral capture.**  Let `P` be the spectral projection of a Hermitian
matrix `H` above `t`.  If `H` has norm at most `1 + delta`, then every
contraction `C` satisfies

`(1 - t) * ‖(1 - P) * C‖² ≤ ‖C - H * C‖ + delta`.

The estimate is dimension independent.  In applications `delta → 0`, so
an almost `H`-fixed contraction is asymptotically captured by `P`.
-/
theorem one_sub_threshold_mul_norm_spectralBelow_mul_sq_le
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (C : Matrix Y Y ℂ)
    (t delta : ℝ) (ht : t ≤ 1) (hdelta : 0 ≤ delta)
    (hHnorm : ‖H‖ ≤ 1 + delta) (hCnorm : ‖C‖ ≤ 1) :
    (1 - t) * ‖spectralBelow H hH t * C‖ ^ 2 ≤
      ‖C - H * C‖ + delta := by
  let U : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let L : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let R : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then 0 else 1)
  let d : Y → ℝ := fun i ↦
    if t < hH.eigenvalues i then 1 - hH.eigenvalues i + delta
    else t - hH.eigenvalues i + delta
  let B : Matrix Y Y ℂ :=
    1 - H + (delta : ℂ) • (1 : Matrix Y Y ℂ) -
      ((1 - t : ℝ) : ℂ) • spectralBelow H hH t
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hHdiag : H = U * L * Uᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = U * L * Uᴴ := by rfl
  have hRdiag : spectralBelow H hH t = U * R * Uᴴ := by
    unfold spectralBelow spectralAbove
    rw [← hUUstar]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : t < hH.eigenvalues i <;> simp [R, hi]
    · simp [R, hij]
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    by_cases hi : t < hH.eigenvalues i
    · simp only [d, hi, if_true]
      have heig := abs_hermitianEigenvalue_le_norm H hH i
      have hupper : hH.eigenvalues i ≤ 1 + delta :=
        (le_abs_self _).trans (heig.trans hHnorm)
      linarith
    · simp only [d, hi, if_false]
      exact add_nonneg (sub_nonneg.mpr (le_of_not_gt hi)) hdelta
  have hBdiag : B = U * Matrix.diagonal (fun i ↦ (d i : ℂ)) * Uᴴ := by
    rw [show B = 1 - H + (delta : ℂ) • 1 -
      ((1 - t : ℝ) : ℂ) • spectralBelow H hH t by rfl,
      hHdiag, hRdiag, ← hUUstar]
    have hdiag :
        (1 : Matrix Y Y ℂ) - L + (delta : ℂ) • 1 -
            ((1 - t : ℝ) : ℂ) • R =
          Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : t < hH.eigenvalues i <;>
          simp [L, R, d, hi] <;> push_cast <;> ring
      · simp [L, R, d, hij]
    rw [← hdiag]
    module
    noncomm_ring
  have hBpos : B.PosSemidef := by
    rw [hBdiag]
    exact (diagonal_posSemidef_of_nonneg d hdnonneg).mul_mul_conjTranspose_same U
  let s : ℝ := Real.sqrt (1 - t)
  let X : Matrix Y Y ℂ :=
    (s : ℂ) • (spectralBelow H hH t * C)
  let K : Matrix Y Y ℂ :=
    Cᴴ * (1 - H) * C + (delta : ℂ) • (Cᴴ * C)
  have hsnonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have hsquare : s ^ 2 = 1 - t := Real.sq_sqrt hsnonneg
  have hRproj := spectralBelow_isOrthogonalProjection H hH t
  have hdom : (K - Xᴴ * X).PosSemidef := by
    have heq : K - Xᴴ * X = Cᴴ * B * C := by
      simp only [K, X, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hRproj.1, B]
      rw [show star (s : ℂ) * (s : ℂ) = ((1 - t : ℝ) : ℂ) by
        rw [map_real, starRingEnd_self_apply, ← Complex.ofReal_mul,
          ← pow_two, hsquare]]
      rw [hRproj.2]
      module
      noncomm_ring
    rw [heq]
    exact hBpos.conjTranspose_mul_mul_same C
  have hnorm := norm_sq_le_norm_of_posSemidef_sub X K hdom
  have hXnorm : ‖X‖ ^ 2 = (1 - t) * ‖spectralBelow H hH t * C‖ ^ 2 := by
    rw [show X = (s : ℂ) • (spectralBelow H hH t * C) by rfl,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsquare]
  rw [hXnorm] at hnorm
  calc
    (1 - t) * ‖spectralBelow H hH t * C‖ ^ 2 ≤ ‖K‖ := hnorm
    _ ≤ ‖C - H * C‖ + delta := by
      rw [show K = Cᴴ * (C - H * C) +
          (delta : ℂ) • (Cᴴ * C) by
        simp only [K]
        noncomm_ring]
      calc
        ‖Cᴴ * (C - H * C) + (delta : ℂ) • (Cᴴ * C)‖ ≤
            ‖Cᴴ * (C - H * C)‖ +
              ‖(delta : ℂ) • (Cᴴ * C)‖ := norm_add_le _ _
        _ ≤ ‖Cᴴ‖ * ‖C - H * C‖ +
              ‖(delta : ℂ)‖ * ‖Cᴴ * C‖ := by
            exact add_le_add (Matrix.l2_opNorm_mul _ _)
              (by rw [norm_smul]; rfl)
        _ ≤ 1 * ‖C - H * C‖ + delta * 1 := by
          have hCstar : ‖Cᴴ‖ ≤ 1 := by simpa using hCnorm
          have hCC : ‖Cᴴ * C‖ ≤ 1 := by
            calc
              ‖Cᴴ * C‖ ≤ ‖Cᴴ‖ * ‖C‖ := Matrix.l2_opNorm_mul _ _
              _ ≤ 1 * 1 := mul_le_mul hCstar hCnorm (norm_nonneg _) zero_le_one
              _ = 1 := one_mul _
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdelta]
          exact add_le_add
            (mul_le_mul_of_nonneg_right hCstar (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hCC hdelta)
        _ = ‖C - H * C‖ + delta := by ring

end KazhdanCornerMatrices
end GroupApproximation
