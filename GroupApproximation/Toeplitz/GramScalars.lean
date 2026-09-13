/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Scalar identities for two isometries with orthogonal ranges

For a unit vector `η` with coordinates `a_i`, the vectors `e_i − conj(a_i) η` have the Gram matrix
`gram a i j = δ_ij − a_i conj(a_j)`, and `∑_{i,j} c_i d_j (gram a i j)²` is computed in
`sum_gram_mul_gram`.  On two blocks of three coordinates, with `βI = ∑ |a_i|²` and `τI = ∑ a_i²`
on the first block and `βJ`, `τJ` on the second, the constants `isoR`, `isoS` and `isoG` make three
such sums equal to `1`, `0` and `1` (`blockCoeff_one_one`, `blockCoeff_one_two`,
`blockCoeff_two_two`).  The constants are bounded and depend continuously on `βI`, `βJ`, `τI`, `τJ`.
-/

namespace GroupApproximation.Toeplitz

noncomputable section

open scoped ComplexConjugate

variable {κ : Type*}

/-- `δ_ij − a_i conj(a_j)`. -/
def gram [DecidableEq κ] (a : κ → ℂ) (i j : κ) : ℂ :=
  (if i = j then 1 else 0) - a i * conj (a j)

theorem sum_gram_mul_gram [Fintype κ] [DecidableEq κ] (a c d : κ → ℂ) :
    ∑ i, ∑ j, gram a i j * (c i * (d j * gram a i j)) =
      ∑ i, c i * d i * (1 - 2 * (a i * conj (a i))) +
        (∑ i, c i * a i ^ 2) * ∑ j, d j * conj (a j) ^ 2 := by
  have h : ∀ i j, gram a i j * (c i * (d j * gram a i j)) =
      (if i = j then c i * d i * (1 - 2 * (a i * conj (a i))) else 0) +
        c i * a i ^ 2 * (d j * conj (a j) ^ 2) := by
    intro i j
    unfold gram
    split_ifs with hij
    · subst hij
      ring
    · ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_mul_sum]

/-- The sum of `sum_gram_mul_gram` when `c` and `d` are constant on the two blocks. -/
theorem sum_gram_mul_gram_blocks (a c d : Fin 3 ⊕ Fin 3 → ℂ) {cI cJ dI dJ : ℂ}
    (hcI : ∀ p, c (Sum.inl p) = cI) (hcJ : ∀ p, c (Sum.inr p) = cJ)
    (hdI : ∀ p, d (Sum.inl p) = dI) (hdJ : ∀ p, d (Sum.inr p) = dJ) :
    ∑ i, ∑ j, gram a i j * (c i * (d j * gram a i j)) =
      cI * dI * (3 - 2 * ∑ p, a (Sum.inl p) * conj (a (Sum.inl p))) +
        cJ * dJ * (3 - 2 * ∑ p, a (Sum.inr p) * conj (a (Sum.inr p))) +
        (cI * ∑ p, a (Sum.inl p) ^ 2 + cJ * ∑ p, a (Sum.inr p) ^ 2) *
          (dI * conj (∑ p, a (Sum.inl p) ^ 2) + dJ * conj (∑ p, a (Sum.inr p) ^ 2)) := by
  rw [sum_gram_mul_gram]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, hcI, hcJ, hdI, hdJ, map_add, map_pow]
  ring

/-- `V = 3 − 2β + |τ|²`. -/
def blockV (β : ℝ) (τ : ℂ) : ℝ := 3 - 2 * β + ‖τ‖ ^ 2

/-- `C = τI conj(τJ)`. -/
def isoC (τI τJ : ℂ) : ℂ := τI * conj τJ

/-- `W = U − |C|²/V`. -/
def isoW (βI βJ : ℝ) (τI τJ : ℂ) : ℝ := blockV βJ τJ - ‖isoC τI τJ‖ ^ 2 / blockV βI τI

/-- `r = 1/√V`. -/
def isoR (βI : ℝ) (τI : ℂ) : ℝ := 1 / Real.sqrt (blockV βI τI)

/-- `s = 1/√W`. -/
def isoS (βI βJ : ℝ) (τI τJ : ℂ) : ℝ := 1 / Real.sqrt (isoW βI βJ τI τJ)

/-- `g = s C / V`. -/
def isoG (βI βJ : ℝ) (τI τJ : ℂ) : ℂ :=
  (isoS βI βJ τI τJ : ℂ) * isoC τI τJ / (blockV βI τI : ℂ)

theorem one_le_blockV {β : ℝ} (hβ : β ≤ 1) (τ : ℂ) : 1 ≤ blockV β τ := by
  unfold blockV
  nlinarith [sq_nonneg ‖τ‖]

theorem blockV_pos {β : ℝ} (hβ : β ≤ 1) (τ : ℂ) : 0 < blockV β τ :=
  lt_of_lt_of_le one_pos (one_le_blockV hβ τ)

theorem blockV_le_four {β : ℝ} (hβ : 0 ≤ β) {τ : ℂ} (hτ : ‖τ‖ ≤ 1) : blockV β τ ≤ 4 := by
  unfold blockV
  nlinarith [norm_nonneg τ]

theorem norm_isoC (τI τJ : ℂ) : ‖isoC τI τJ‖ = ‖τI‖ * ‖τJ‖ := by
  rw [isoC, norm_mul, Complex.norm_conj]

theorem one_le_blockV_mul_sub {βI βJ : ℝ} (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) (τI τJ : ℂ) :
    1 ≤ blockV βJ τJ * blockV βI τI - ‖isoC τI τJ‖ ^ 2 := by
  rw [norm_isoC]
  unfold blockV
  nlinarith [mul_le_mul (by linarith : (1 : ℝ) ≤ 3 - 2 * βJ) (by linarith : (1 : ℝ) ≤ 3 - 2 * βI)
      zero_le_one (by linarith), mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - 2 * βJ) (sq_nonneg ‖τI‖),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - 2 * βI) (sq_nonneg ‖τJ‖)]

theorem isoW_mul_blockV {βI : ℝ} (hβI : βI ≤ 1) (βJ : ℝ) (τI τJ : ℂ) :
    isoW βI βJ τI τJ * blockV βI τI = blockV βJ τJ * blockV βI τI - ‖isoC τI τJ‖ ^ 2 := by
  rw [isoW, sub_mul, div_mul_cancel₀ _ (blockV_pos hβI τI).ne']

theorem isoW_pos {βI βJ : ℝ} (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) (τI τJ : ℂ) :
    0 < isoW βI βJ τI τJ := by
  have hWV := isoW_mul_blockV hβI βJ τI τJ
  have h1 := one_le_blockV_mul_sub hβI hβJ τI τJ
  have hV := blockV_pos hβI τI
  by_contra h
  rw [not_lt] at h
  nlinarith

theorem quarter_le_isoW {βI βJ : ℝ} (hβI0 : 0 ≤ βI) (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) {τI : ℂ}
    (hτI : ‖τI‖ ≤ 1) (τJ : ℂ) : 1 / 4 ≤ isoW βI βJ τI τJ := by
  have hV := blockV_le_four hβI0 hτI
  have hWV := isoW_mul_blockV hβI βJ τI τJ
  have h1 := one_le_blockV_mul_sub hβI hβJ τI τJ
  by_contra h
  rw [not_le] at h
  nlinarith [mul_pos (sub_pos.2 h) (blockV_pos hβI τI)]

theorem isoR_sq_mul_blockV {βI : ℝ} (hβI : βI ≤ 1) (τI : ℂ) :
    isoR βI τI ^ 2 * blockV βI τI = 1 := by
  rw [isoR, div_pow, one_pow, Real.sq_sqrt (blockV_pos hβI τI).le,
    one_div_mul_cancel (blockV_pos hβI τI).ne']

theorem isoS_sq_mul_isoW {βI βJ : ℝ} (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) (τI τJ : ℂ) :
    isoS βI βJ τI τJ ^ 2 * isoW βI βJ τI τJ = 1 := by
  rw [isoS, div_pow, one_pow, Real.sq_sqrt (isoW_pos hβI hβJ τI τJ).le,
    one_div_mul_cancel (isoW_pos hβI hβJ τI τJ).ne']

theorem isoR_nonneg (βI : ℝ) (τI : ℂ) : 0 ≤ isoR βI τI :=
  div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem isoS_nonneg (βI βJ : ℝ) (τI τJ : ℂ) : 0 ≤ isoS βI βJ τI τJ :=
  div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem isoR_le_one {βI : ℝ} (hβI : βI ≤ 1) (τI : ℂ) : isoR βI τI ≤ 1 := by
  have h := isoR_sq_mul_blockV hβI τI
  have hV := one_le_blockV hβI τI
  have h0 := isoR_nonneg βI τI
  by_contra hr
  rw [not_le] at hr
  nlinarith [mul_pos (mul_pos (sub_pos.2 hr) (by linarith : (0 : ℝ) < isoR βI τI + 1))
    (blockV_pos hβI τI)]

theorem isoS_le_two {βI βJ : ℝ} (hβI0 : 0 ≤ βI) (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) {τI : ℂ}
    (hτI : ‖τI‖ ≤ 1) (τJ : ℂ) : isoS βI βJ τI τJ ≤ 2 := by
  have h := isoS_sq_mul_isoW hβI hβJ τI τJ
  have hW := quarter_le_isoW hβI0 hβI hβJ hτI τJ
  have h0 := isoS_nonneg βI βJ τI τJ
  by_contra hs
  rw [not_le] at hs
  nlinarith [mul_pos (mul_pos (sub_pos.2 hs) (by linarith : (0 : ℝ) < isoS βI βJ τI τJ + 2))
    (isoW_pos hβI hβJ τI τJ)]

theorem norm_isoG_le_two {βI βJ : ℝ} (hβI0 : 0 ≤ βI) (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) {τI τJ : ℂ}
    (hτI : ‖τI‖ ≤ 1) (hτJ : ‖τJ‖ ≤ 1) : ‖isoG βI βJ τI τJ‖ ≤ 2 := by
  have hV := one_le_blockV hβI τI
  have hs := isoS_le_two hβI0 hβI hβJ hτI τJ
  have hs0 := isoS_nonneg βI βJ τI τJ
  have hC : ‖isoC τI τJ‖ ≤ 1 := by
    rw [norm_isoC]
    nlinarith [norm_nonneg τI, norm_nonneg τJ]
  rw [isoG, norm_div, norm_mul, Complex.norm_of_nonneg hs0,
    Complex.norm_of_nonneg (blockV_pos hβI τI).le, div_le_iff₀ (blockV_pos hβI τI)]
  nlinarith [norm_nonneg (isoC τI τJ)]

theorem mul_conj_eq_norm_sq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem blockV_ofReal (β : ℝ) (τ : ℂ) : 3 - 2 * (β : ℂ) + τ * conj τ = (blockV β τ : ℂ) := by
  rw [mul_conj_eq_norm_sq]
  unfold blockV
  norm_cast

theorem blockCoeff_one_one {βI : ℝ} (hβI : βI ≤ 1) (τI τJ bJ : ℂ) :
    (isoR βI τI : ℂ) * isoR βI τI * (3 - 2 * βI) + 0 * 0 * (3 - 2 * bJ) +
      ((isoR βI τI : ℂ) * τI + 0 * τJ) * ((isoR βI τI : ℂ) * conj τI + 0 * conj τJ) = 1 := by
  have hV := blockV_ofReal βI τI
  have hr : (isoR βI τI : ℂ) ^ 2 * blockV βI τI = 1 := by
    exact_mod_cast isoR_sq_mul_blockV hβI τI
  linear_combination (isoR βI τI : ℂ) ^ 2 * hV + hr

theorem blockCoeff_one_two {βI : ℝ} (hβI : βI ≤ 1) (βJ : ℝ) (τI τJ bJ : ℂ) :
    (isoR βI τI : ℂ) * -isoG βI βJ τI τJ * (3 - 2 * βI) +
        0 * (isoS βI βJ τI τJ : ℂ) * (3 - 2 * bJ) +
      ((isoR βI τI : ℂ) * τI + 0 * τJ) *
        (-isoG βI βJ τI τJ * conj τI + (isoS βI βJ τI τJ : ℂ) * conj τJ) = 0 := by
  have hV := blockV_ofReal βI τI
  have hg : isoG βI βJ τI τJ * blockV βI τI = isoS βI βJ τI τJ * (τI * conj τJ) :=
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 (blockV_pos hβI τI).ne')
  linear_combination (-(isoR βI τI : ℂ) * isoG βI βJ τI τJ) * hV - (isoR βI τI : ℂ) * hg

theorem blockCoeff_two_two {βI βJ : ℝ} (hβI : βI ≤ 1) (hβJ : βJ ≤ 1) (τI τJ : ℂ) :
    -conj (isoG βI βJ τI τJ) * -isoG βI βJ τI τJ * (3 - 2 * βI) +
        (isoS βI βJ τI τJ : ℂ) * isoS βI βJ τI τJ * (3 - 2 * βJ) +
      (-conj (isoG βI βJ τI τJ) * τI + (isoS βI βJ τI τJ : ℂ) * τJ) *
        (-isoG βI βJ τI τJ * conj τI + (isoS βI βJ τI τJ : ℂ) * conj τJ) = 1 := by
  have hV0 : (blockV βI τI : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (blockV_pos hβI τI).ne'
  have hV := blockV_ofReal βI τI
  have hU := blockV_ofReal βJ τJ
  have hg : isoG βI βJ τI τJ * blockV βI τI = isoS βI βJ τI τJ * (τI * conj τJ) :=
    div_mul_cancel₀ _ hV0
  have hCC : τI * conj τJ * (conj τI * τJ) = ((‖isoC τI τJ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mul_conj_eq_norm_sq, isoC, map_mul, Complex.conj_conj]
  have hW : (isoW βI βJ τI τJ : ℂ) * blockV βI τI =
      blockV βJ τJ * blockV βI τI - τI * conj τJ * (conj τI * τJ) := by
    rw [hCC]
    exact_mod_cast isoW_mul_blockV hβI βJ τI τJ
  have hs : (isoS βI βJ τI τJ : ℂ) ^ 2 * isoW βI βJ τI τJ = 1 := by
    exact_mod_cast isoS_sq_mul_isoW hβI hβJ τI τJ
  have hX : (-conj (isoG βI βJ τI τJ) * -isoG βI βJ τI τJ * (3 - 2 * βI) +
        (isoS βI βJ τI τJ : ℂ) * isoS βI βJ τI τJ * (3 - 2 * βJ) +
      (-conj (isoG βI βJ τI τJ) * τI + (isoS βI βJ τI τJ : ℂ) * τJ) *
        (-isoG βI βJ τI τJ * conj τI + (isoS βI βJ τI τJ : ℂ) * conj τJ) - 1) *
      blockV βI τI = 0 := by
    linear_combination (conj (isoG βI βJ τI τJ) * isoG βI βJ τI τJ * blockV βI τI) * hV +
      ((isoS βI βJ τI τJ : ℂ) ^ 2 * blockV βI τI) * hU +
      (conj (isoG βI βJ τI τJ) * blockV βI τI) * hg -
      ((isoS βI βJ τI τJ : ℂ) * (conj τI * τJ)) * hg -
      (isoS βI βJ τI τJ : ℂ) ^ 2 * hW + (blockV βI τI : ℂ) * hs
  exact sub_eq_zero.1 ((mul_eq_zero.1 hX).resolve_right hV0)

theorem continuous_blockV {X : Type*} [TopologicalSpace X] {β : X → ℝ} {τ : X → ℂ}
    (hβ : Continuous β) (hτ : Continuous τ) : Continuous fun x => blockV (β x) (τ x) :=
  (continuous_const.sub (continuous_const.mul hβ)).add (hτ.norm.pow 2)

theorem continuous_isoC {X : Type*} [TopologicalSpace X] {τI τJ : X → ℂ} (hτI : Continuous τI)
    (hτJ : Continuous τJ) : Continuous fun x => isoC (τI x) (τJ x) :=
  hτI.mul (Complex.continuous_conj.comp hτJ)

theorem continuous_isoR {X : Type*} [TopologicalSpace X] {βI : X → ℝ} {τI : X → ℂ}
    (hβI1 : ∀ x, βI x ≤ 1) (hβI : Continuous βI) (hτI : Continuous τI) :
    Continuous fun x => isoR (βI x) (τI x) :=
  continuous_const.div (continuous_blockV hβI hτI).sqrt fun x =>
    (Real.sqrt_pos.2 (blockV_pos (hβI1 x) _)).ne'

theorem continuous_isoW {X : Type*} [TopologicalSpace X] {βI βJ : X → ℝ} {τI τJ : X → ℂ}
    (hβI1 : ∀ x, βI x ≤ 1) (hβI : Continuous βI) (hβJ : Continuous βJ) (hτI : Continuous τI)
    (hτJ : Continuous τJ) : Continuous fun x => isoW (βI x) (βJ x) (τI x) (τJ x) :=
  (continuous_blockV hβJ hτJ).sub (((continuous_isoC hτI hτJ).norm.pow 2).div
    (continuous_blockV hβI hτI) fun x => (blockV_pos (hβI1 x) _).ne')

theorem continuous_isoS {X : Type*} [TopologicalSpace X] {βI βJ : X → ℝ} {τI τJ : X → ℂ}
    (hβI1 : ∀ x, βI x ≤ 1) (hβJ1 : ∀ x, βJ x ≤ 1) (hβI : Continuous βI) (hβJ : Continuous βJ)
    (hτI : Continuous τI) (hτJ : Continuous τJ) :
    Continuous fun x => isoS (βI x) (βJ x) (τI x) (τJ x) :=
  continuous_const.div (continuous_isoW hβI1 hβI hβJ hτI hτJ).sqrt fun x =>
    (Real.sqrt_pos.2 (isoW_pos (hβI1 x) (hβJ1 x) _ _)).ne'

theorem continuous_isoG {X : Type*} [TopologicalSpace X] {βI βJ : X → ℝ} {τI τJ : X → ℂ}
    (hβI1 : ∀ x, βI x ≤ 1) (hβJ1 : ∀ x, βJ x ≤ 1) (hβI : Continuous βI) (hβJ : Continuous βJ)
    (hτI : Continuous τI) (hτJ : Continuous τJ) :
    Continuous fun x => isoG (βI x) (βJ x) (τI x) (τJ x) :=
  ((Complex.continuous_ofReal.comp (continuous_isoS hβI1 hβJ1 hβI hβJ hτI hτJ)).mul
    (continuous_isoC hτI hτJ)).div (Complex.continuous_ofReal.comp (continuous_blockV hβI hτI))
    fun x => Complex.ofReal_ne_zero.2 (blockV_pos (hβI1 x) _).ne'

end

end GroupApproximation.Toeplitz
