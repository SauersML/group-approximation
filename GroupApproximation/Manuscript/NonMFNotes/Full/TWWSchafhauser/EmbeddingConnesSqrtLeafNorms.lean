import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDefs

/-!
# Square-root control, part 1: norm and Hilbert--Schmidt toolbox

Lane TWWSch3b1B (work order WO-3b1-B).  Manuscript: `non_mf_group_notes.tex`, the
Tikuisis--White--Winter input used in Schafhauser's §3 (Connes' trick; Brown--Ozawa
Thm 6.2.7 and the Powers--Størmer inequality).  This file holds the elementary facts
consumed by `EmbeddingConnesSqrtLeafAbstract`:

* `SqrtLeaf.norm_le_one_of_conjTranspose_mul_self`: `A⋆A = B`, `‖B‖ ≤ 1` give `‖A‖ ≤ 1`;
* `SqrtLeaf.norm_one_le`, `SqrtLeaf.norm_proj_le_one`: projections are contractions;
* `SqrtLeaf.re_trace_conjTranspose_mul_self_nonneg`: `0 ≤ ‖A‖₂²`;
* `SqrtLeaf.re_trace_conjTranspose_mul_symm`: `re tr(Y⋆X) = re tr(X⋆Y)`;
* `SqrtLeaf.two_mul_re_trace_le`: the real-scalar AM--GM inequality
  `2c re tr(X⋆Y) ≤ c² ‖X‖₂² + ‖Y‖₂²`, from `‖cX − Y‖₂² ≥ 0`.

Here `‖M‖₂² = re tr(M⋆M)` is the unnormalized Hilbert--Schmidt norm, as in
`ContractionSqrtCommutatorControl`.
-/

namespace GroupApproximation.Full.TWWSchafhauser.SqrtLeaf

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix whose Gram matrix is a contraction is a contraction (`‖A‖² = ‖A⋆A‖`). -/
theorem norm_le_one_of_conjTranspose_mul_self {A B : Matrix n n ℂ} (h : Aᴴ * A = B)
    (hB : ‖B‖ ≤ 1) : ‖A‖ ≤ 1 := by
  have h1 : ‖A‖ * ‖A‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, h]
    exact hB
  nlinarith [norm_nonneg A]

/-- The identity matrix is a contraction (also for the empty index type). -/
theorem norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix n n ℂ)‖ = ‖(1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_one, Matrix.mul_one]
  nlinarith [norm_nonneg (1 : Matrix n n ℂ)]

/-- An orthogonal projection is a contraction. -/
theorem norm_proj_le_one {p : Matrix n n ℂ} (hpH : pᴴ = p) (hpp : p * p = p) : ‖p‖ ≤ 1 := by
  have h1 : ‖p‖ = ‖p‖ * ‖p‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hpH, hpp]
  nlinarith [norm_nonneg p]

/-- The Hilbert--Schmidt square `re tr(A⋆A)` is nonnegative. -/
theorem re_trace_conjTranspose_mul_self_nonneg (A : Matrix n n ℂ) :
    0 ≤ (trace (Aᴴ * A)).re :=
  (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self A).trace_nonneg).1

/-- `re tr(Y⋆X) = re tr(X⋆Y)`: the two traces are complex conjugate. -/
theorem re_trace_conjTranspose_mul_symm (X Y : Matrix n n ℂ) :
    (trace (Yᴴ * X)).re = (trace (Xᴴ * Y)).re := by
  have h : Yᴴ * X = (Xᴴ * Y)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [h, Matrix.trace_conjTranspose]
  exact Complex.conj_re _

/-- Expansion of `(cX − Y)⋆(cX − Y)` for a real scalar `c`. -/
theorem conjTranspose_smul_sub_mul (c : ℝ) (X Y : Matrix n n ℂ) :
    (c • X - Y)ᴴ * (c • X - Y) =
      (c * c) • (Xᴴ * X) - c • (Xᴴ * Y) - c • (Yᴴ * X) + Yᴴ * Y := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, smul_smul]
  abel

/-- **AM--GM for Hilbert--Schmidt pairings.**  For real `c`,
`2c re tr(X⋆Y) ≤ c² re tr(X⋆X) + re tr(Y⋆Y)`. -/
theorem two_mul_re_trace_le (c : ℝ) (X Y : Matrix n n ℂ) :
    2 * c * (trace (Xᴴ * Y)).re ≤ c ^ 2 * (trace (Xᴴ * X)).re + (trace (Yᴴ * Y)).re := by
  have h0 := re_trace_conjTranspose_mul_self_nonneg (c • X - Y)
  rw [conjTranspose_smul_sub_mul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Complex.add_re, Complex.sub_re,
    Complex.sub_re, Complex.smul_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, re_trace_conjTranspose_mul_symm X Y] at h0
  nlinarith [h0]

/-- AM--GM in the form used for error terms: if `‖X‖₂² ≤ A` and `‖Y‖₂² ≤ B` then
`−2c re tr(X⋆Y) ≤ c² A + B` for every real `c`. -/
theorem neg_two_mul_re_trace_le {c A B : ℝ} (X Y : Matrix n n ℂ)
    (hX : (trace (Xᴴ * X)).re ≤ A) (hY : (trace (Yᴴ * Y)).re ≤ B) :
    -(2 * c * (trace (Xᴴ * Y)).re) ≤ c ^ 2 * A + B := by
  have h := two_mul_re_trace_le (-c) X Y
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith [mul_le_mul_of_nonneg_left hX hc2]

/-- AM--GM in the form used for the main term: `2c re tr(X⋆Y) ≤ c² A + B`. -/
theorem two_mul_re_trace_le_of {c A B : ℝ} (X Y : Matrix n n ℂ)
    (hX : (trace (Xᴴ * X)).re ≤ A) (hY : (trace (Yᴴ * Y)).re ≤ B) :
    2 * c * (trace (Xᴴ * Y)).re ≤ c ^ 2 * A + B := by
  have h := two_mul_re_trace_le c X Y
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith [mul_le_mul_of_nonneg_left hX hc2]

end

end GroupApproximation.Full.TWWSchafhauser.SqrtLeaf
