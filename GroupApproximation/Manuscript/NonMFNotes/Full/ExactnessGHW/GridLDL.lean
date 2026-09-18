import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.GridRounding
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Rational Gram--Schmidt and dyadic scaling

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform` (the Guentner--Higson--Weinberger property A step for
`Σ ≤ GL₄(ℚ)`): the rational `LDL` decomposition behind the dyadic grid
approximation.  Rows of `γ ∈ GL₄(ℚ)` are orthogonalised from the bottom,
`γ = uni(…) · Y` with the rows of `Y` pairwise orthogonal and nonzero, and each
row is scaled by a power `2^{s_i}` with `4^{s_i} ≤ ‖Y_i‖² < 4^{s_i+1}`.  All
estimates are rational (`|z i j|² ≤ ‖z_i‖² < 4`), without square roots.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel

/-- Gram--Schmidt coefficient `⟨u, w⟩ / ⟨w, w⟩`. -/
def gsProj (u w : Fin 4 → ℚ) : ℚ :=
  (u ⬝ᵥ w) / (w ⬝ᵥ w)

theorem gsProj_mul (u w : Fin 4 → ℚ) (hw : w ⬝ᵥ w ≠ 0) :
    gsProj u w * (w ⬝ᵥ w) = u ⬝ᵥ w :=
  div_mul_cancel₀ _ hw

/-- Bottom row of the Gram--Schmidt matrix. -/
def gs3 (A : Mat) : Fin 4 → ℚ :=
  A 3

/-- Third row of the Gram--Schmidt matrix. -/
def gs2 (A : Mat) : Fin 4 → ℚ :=
  A 2 - gsProj (A 2) (gs3 A) • gs3 A

/-- Second row of the Gram--Schmidt matrix. -/
def gs1 (A : Mat) : Fin 4 → ℚ :=
  A 1 - gsProj (A 1) (gs2 A) • gs2 A - gsProj (A 1) (gs3 A) • gs3 A

/-- Top row of the Gram--Schmidt matrix. -/
def gs0 (A : Mat) : Fin 4 → ℚ :=
  A 0 - gsProj (A 0) (gs1 A) • gs1 A - gsProj (A 0) (gs2 A) • gs2 A -
    gsProj (A 0) (gs3 A) • gs3 A

/-- The Gram--Schmidt matrix with rows orthogonalised from the bottom. -/
def gsY (A : Mat) : Mat :=
  Matrix.of ![gs0 A, gs1 A, gs2 A, gs3 A]

/-- Row operations performed by a unitriangular matrix. -/
theorem uni_mul_of (a b c d e f : ℚ) (v0 v1 v2 v3 : Fin 4 → ℚ) :
    uni a b c d e f * Matrix.of ![v0, v1, v2, v3] =
      Matrix.of ![v0 + a • v1 + b • v2 + c • v3, v1 + d • v2 + e • v3, v2 + f • v3, v3] :=
  Matrix.ext fun i j => by
    fin_cases i <;> simp [uni, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- `A = uni(…) · gsY A`. -/
theorem gs_eq (A : Mat) : ∃ a b c d e f : ℚ, A = uni a b c d e f * gsY A := by
  refine ⟨gsProj (A 0) (gs1 A), gsProj (A 0) (gs2 A), gsProj (A 0) (gs3 A),
    gsProj (A 1) (gs2 A), gsProj (A 1) (gs3 A), gsProj (A 2) (gs3 A), ?_⟩
  rw [gsY, uni_mul_of]
  have h0 : gs0 A + gsProj (A 0) (gs1 A) • gs1 A + gsProj (A 0) (gs2 A) • gs2 A +
      gsProj (A 0) (gs3 A) • gs3 A = A 0 := by
    rw [gs0]
    abel
  have h1 : gs1 A + gsProj (A 1) (gs2 A) • gs2 A + gsProj (A 1) (gs3 A) • gs3 A = A 1 := by
    rw [gs1]
    abel
  have h2 : gs2 A + gsProj (A 2) (gs3 A) • gs3 A = A 2 := by
    rw [gs2]
    abel
  refine Matrix.ext fun i j => ?_
  fin_cases i
  · exact (congrFun h0 j).symm
  · exact (congrFun h1 j).symm
  · exact (congrFun h2 j).symm
  · rfl

/-- The Gram--Schmidt matrix of a unit has a right inverse. -/
theorem gsY_mul_eq_one (γ : Matˣ) : ∃ X : Mat, gsY (γ : Mat) * X = 1 := by
  obtain ⟨a, b, c, d, e, f, h⟩ := gs_eq (γ : Mat)
  refine ⟨((γ⁻¹ : Matˣ) : Mat) * uni a b c d e f, ?_⟩
  calc gsY (γ : Mat) * (((γ⁻¹ : Matˣ) : Mat) * uni a b c d e f)
      = uniInv a b c d e f * (uni a b c d e f * gsY (γ : Mat)) * ((γ⁻¹ : Matˣ) : Mat) *
          uni a b c d e f := by
        rw [← mul_assoc (uniInv a b c d e f), uniInv_mul_uni, one_mul, mul_assoc]
    _ = 1 := by
        rw [← h, mul_assoc (uniInv a b c d e f), Units.mul_inv, mul_one, uniInv_mul_uni]

/-- The rows of the Gram--Schmidt matrix of a unit are nonzero. -/
theorem gsY_self_pos (γ : Matˣ) (i : Fin 4) : 0 < gsY (γ : Mat) i ⬝ᵥ gsY (γ : Mat) i := by
  obtain ⟨X, hX⟩ := gsY_mul_eq_one γ
  refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => mul_self_nonneg _) fun h => ?_
  have h0 : gsY (γ : Mat) i = 0 := dotProduct_self_eq_zero.mp h.symm
  have h1 : (gsY (γ : Mat) * X) i i = 1 := by
    rw [hX, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, h0] at h1
  simp at h1

theorem gs_orth23 (A : Mat) (h3 : gs3 A ⬝ᵥ gs3 A ≠ 0) : gs2 A ⬝ᵥ gs3 A = 0 := by
  have hp := gsProj_mul (A 2) (gs3 A) h3
  simp only [gs2, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination -hp

theorem gs_orth13 (A : Mat) (h3 : gs3 A ⬝ᵥ gs3 A ≠ 0) (h23 : gs2 A ⬝ᵥ gs3 A = 0) :
    gs1 A ⬝ᵥ gs3 A = 0 := by
  have hp := gsProj_mul (A 1) (gs3 A) h3
  simp only [gs1, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination -gsProj (A 1) (gs2 A) * h23 - hp

theorem gs_orth12 (A : Mat) (h2 : gs2 A ⬝ᵥ gs2 A ≠ 0) (h23 : gs2 A ⬝ᵥ gs3 A = 0) :
    gs1 A ⬝ᵥ gs2 A = 0 := by
  have hp := gsProj_mul (A 1) (gs2 A) h2
  have h32 : gs3 A ⬝ᵥ gs2 A = 0 := (dotProduct_comm _ _).trans h23
  simp only [gs1, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination -hp - gsProj (A 1) (gs3 A) * h32

theorem gs_orth03 (A : Mat) (h3 : gs3 A ⬝ᵥ gs3 A ≠ 0) (h13 : gs1 A ⬝ᵥ gs3 A = 0)
    (h23 : gs2 A ⬝ᵥ gs3 A = 0) : gs0 A ⬝ᵥ gs3 A = 0 := by
  have hp := gsProj_mul (A 0) (gs3 A) h3
  simp only [gs0, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination -hp - gsProj (A 0) (gs1 A) * h13 - gsProj (A 0) (gs2 A) * h23

theorem gs_orth02 (A : Mat) (h2 : gs2 A ⬝ᵥ gs2 A ≠ 0) (h12 : gs1 A ⬝ᵥ gs2 A = 0)
    (h23 : gs2 A ⬝ᵥ gs3 A = 0) : gs0 A ⬝ᵥ gs2 A = 0 := by
  have hp := gsProj_mul (A 0) (gs2 A) h2
  have h32 : gs3 A ⬝ᵥ gs2 A = 0 := (dotProduct_comm _ _).trans h23
  simp only [gs0, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination -hp - gsProj (A 0) (gs1 A) * h12 - gsProj (A 0) (gs3 A) * h32

theorem gs_orth01 (A : Mat) (h1 : gs1 A ⬝ᵥ gs1 A ≠ 0) (h12 : gs1 A ⬝ᵥ gs2 A = 0)
    (h13 : gs1 A ⬝ᵥ gs3 A = 0) : gs0 A ⬝ᵥ gs1 A = 0 := by
  have hp := gsProj_mul (A 0) (gs1 A) h1
  have h21 : gs2 A ⬝ᵥ gs1 A = 0 := (dotProduct_comm _ _).trans h12
  have h31 : gs3 A ⬝ᵥ gs1 A = 0 := (dotProduct_comm _ _).trans h13
  simp only [gs0, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination -hp - gsProj (A 0) (gs2 A) * h21 - gsProj (A 0) (gs3 A) * h31

/-- The rows of the Gram--Schmidt matrix of a unit are pairwise orthogonal. -/
theorem gsY_orth (γ : Matˣ) (i j : Fin 4) (hij : i ≠ j) :
    gsY (γ : Mat) i ⬝ᵥ gsY (γ : Mat) j = 0 := by
  have hp := gsY_self_pos γ
  have h3 : gs3 (γ : Mat) ⬝ᵥ gs3 (γ : Mat) ≠ 0 := (hp 3).ne'
  have h2 : gs2 (γ : Mat) ⬝ᵥ gs2 (γ : Mat) ≠ 0 := (hp 2).ne'
  have h1 : gs1 (γ : Mat) ⬝ᵥ gs1 (γ : Mat) ≠ 0 := (hp 1).ne'
  have h23 := gs_orth23 (γ : Mat) h3
  have h13 := gs_orth13 (γ : Mat) h3 h23
  have h12 := gs_orth12 (γ : Mat) h2 h23
  have h03 := gs_orth03 (γ : Mat) h3 h13 h23
  have h02 := gs_orth02 (γ : Mat) h2 h12 h23
  have h01 := gs_orth01 (γ : Mat) h1 h12 h13
  revert hij
  fin_cases i <;> fin_cases j
  · exact fun h => absurd rfl h
  · exact fun _ => h01
  · exact fun _ => h02
  · exact fun _ => h03
  · exact fun _ => (dotProduct_comm _ _).trans h01
  · exact fun h => absurd rfl h
  · exact fun _ => h12
  · exact fun _ => h13
  · exact fun _ => (dotProduct_comm _ _).trans h02
  · exact fun _ => (dotProduct_comm _ _).trans h12
  · exact fun h => absurd rfl h
  · exact fun _ => h23
  · exact fun _ => (dotProduct_comm _ _).trans h03
  · exact fun _ => (dotProduct_comm _ _).trans h13
  · exact fun _ => (dotProduct_comm _ _).trans h23
  · exact fun h => absurd rfl h

/-- **Dyadic scaling** of a matrix with nonzero orthogonal rows:
`Y = diag(2^s) · z` with `z` and a right inverse `zt` of `z` having entries
bounded by `2`. -/
theorem exists_dyadic_scaling {Y : Mat} (hpos : ∀ i, 0 < Y i ⬝ᵥ Y i)
    (horth : ∀ i j, i ≠ j → Y i ⬝ᵥ Y j = 0) :
    ∃ s : Fin 4 → ℤ, ∃ z zt : Mat, Y = twoDiag s * z ∧ z * zt = 1 ∧
      (∀ i j, |z i j| ≤ 2) ∧ (∀ i j, |zt i j| ≤ 2) := by
  choose s hs using fun i => exists_mem_Ico_zpow (hpos i) (by norm_num : (1 : ℚ) < 4)
  have ht : ∀ i, (2 : ℚ) ^ s i ≠ 0 := fun i => zpow_ne_zero _ (by norm_num)
  have h4pos : ∀ i, (0 : ℚ) < 4 ^ s i := fun i => zpow_pos (by norm_num) _
  have h4 : ∀ i, (2 : ℚ) ^ s i * 2 ^ s i = 4 ^ s i := fun i => by
    rw [← mul_zpow]
    norm_num
  obtain ⟨z, hz⟩ : ∃ z : Mat, ∀ i j, z i j = Y i j / 2 ^ s i :=
    ⟨Matrix.of fun i j => Y i j / 2 ^ s i, fun _ _ => rfl⟩
  have hY : Y = twoDiag s * z := Matrix.ext fun i j => by
    simp only [twoDiag, Matrix.diagonal_mul, hz]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ht i)]
  have hzd : ∀ i j, z i ⬝ᵥ z j = (Y i ⬝ᵥ Y j) / (2 ^ s i * 2 ^ s j) := fun i j => by
    simp only [dotProduct, hz, Finset.sum_div, div_mul_div_comm]
  have he1 : ∀ i, 1 ≤ z i ⬝ᵥ z i := fun i => by
    rw [hzd, h4, le_div_iff₀ (h4pos i), one_mul]
    exact (hs i).1
  have he4 : ∀ i, z i ⬝ᵥ z i < 4 := fun i => by
    have hlt := (hs i).2
    rw [zpow_add_one₀ (by norm_num : (4 : ℚ) ≠ 0)] at hlt
    rw [hzd, h4, div_lt_iff₀ (h4pos i)]
    linarith
  have hzo : ∀ i j, i ≠ j → z i ⬝ᵥ z j = 0 := fun i j hij => by
    rw [hzd, horth i j hij, zero_div]
  have hzb : ∀ i j, |z i j| ≤ 2 := fun i j => by
    have h1 : z i j * z i j ≤ z i ⬝ᵥ z i :=
      Finset.single_le_sum (f := fun k => z i k * z i k) (fun k _ => mul_self_nonneg (z i k))
        (Finset.mem_univ j)
    have h2 := he4 i
    exact abs_le_of_sq_le_sq (by rw [sq, sq]; linarith) (by norm_num)
  obtain ⟨zt, hzt⟩ : ∃ zt : Mat, ∀ i j, zt i j = z j i / (z j ⬝ᵥ z j) :=
    ⟨Matrix.of fun i j => z j i / (z j ⬝ᵥ z j), fun _ _ => rfl⟩
  have hmul : z * zt = 1 := Matrix.ext fun i j => by
    have h : (z * zt) i j = (z i ⬝ᵥ z j) / (z j ⬝ᵥ z j) := by
      simp only [Matrix.mul_apply, hzt, dotProduct, Finset.sum_div, mul_div_assoc]
    rw [h]
    by_cases hij : i = j
    · rw [hij, div_self (lt_of_lt_of_le one_pos (he1 j)).ne', Matrix.one_apply_eq]
    · rw [hzo i j hij, zero_div, Matrix.one_apply_ne hij]
  have hztb : ∀ i j, |zt i j| ≤ 2 := fun i j => by
    rw [hzt, abs_div, abs_of_pos (lt_of_lt_of_le one_pos (he1 j))]
    exact (div_le_self (abs_nonneg _) (he1 j)).trans (hzb j i)
  exact ⟨s, z, zt, hY, hmul, hzb, hztb⟩

end GroupApproximation.Full.NN09b
