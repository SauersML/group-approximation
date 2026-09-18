import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.GridLDL
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Every element of `GL₄(ℚ)` is near a dyadic grid point

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform` (the Guentner--Higson--Weinberger property A step for
`Σ ≤ GL₄(ℚ)`): for `γ ∈ GL₄(ℚ)` write `γ = uni(…) · Y` (rational Gram--Schmidt,
`GridLDL`), `Y = diag(2^s) · z` (dyadic scaling), conjugate
`uni(…) · diag(2^s) = diag(2^s) · V` with `V` unitriangular, and round
`V = m · g` with `m` integral unitriangular and the parameters of `g` in
`[0, 1)` (`GridRounding`).  The grid point `b = diag(2^s) · m` satisfies
`b⁻¹ γ = g z` and `γ⁻¹ b = zt g⁻¹`, whose entries are bounded by `16`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel

/-- Entry bound for a product of `4 × 4` matrices. -/
theorem abs_mul_apply_le_of_bound {a b : Mat} {A B : ℚ} (ha : ∀ i j, |a i j| ≤ A)
    (hb : ∀ i j, |b i j| ≤ B) (i j : Fin 4) : |(a * b) i j| ≤ 4 * (A * B) := by
  rw [Matrix.mul_apply]
  calc |∑ k, a i k * b k j| ≤ ∑ k, |a i k * b k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 4, A * B := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact mul_le_mul (ha i k) (hb k j) (abs_nonneg _) ((abs_nonneg _).trans (ha i k))
    _ = 4 * (A * B) := by
        rw [Fin.sum_univ_four]
        ring

/-- Conjugating a unitriangular matrix by a dyadic diagonal matrix. -/
theorem uni_mul_twoDiag (a b c d e f : ℚ) (s : Fin 4 → ℤ) :
    ∃ V : Mat, uni a b c d e f * twoDiag s = twoDiag s * V ∧ IsUpperTri V ∧
      ∀ i, V i i = 1 := by
  have ht : ∀ i, (2 : ℚ) ^ s i ≠ 0 := fun i => zpow_ne_zero _ (by norm_num)
  obtain ⟨V, hV⟩ : ∃ V : Mat, ∀ i j, V i j = uni a b c d e f i j * 2 ^ s j / 2 ^ s i :=
    ⟨Matrix.of fun i j => uni a b c d e f i j * 2 ^ s j / 2 ^ s i, fun _ _ => rfl⟩
  refine ⟨V, Matrix.ext fun i j => ?_, fun i j hji => ?_, fun i => ?_⟩
  · simp only [twoDiag, Matrix.mul_diagonal, Matrix.diagonal_mul, hV]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ht i)]
  · rw [hV, isUpperTri_uni a b c d e f i j hji, zero_mul, zero_div]
  · rw [hV, uni_apply_diag, one_mul, div_self (ht i)]

/-- The dyadic grid point `diag(2^s) · uni(p, B, C, q, E, r)`. -/
def gridUnit (s : Fin 4 → ℤ) (p B C q E r : ℤ) : Matˣ where
  val := twoDiag s * uni p B C q E r
  inv := uniInv p B C q E r * twoDiag (-s)
  val_inv := by
    rw [mul_assoc, ← mul_assoc (uni p B C q E r), uni_mul_uniInv, one_mul,
      twoDiag_mul_twoDiag_neg]
  inv_val := by
    rw [mul_assoc, ← mul_assoc (twoDiag (-s)), twoDiag_mul, neg_add_cancel, twoDiag_zero,
      one_mul, uniInv_mul_uni]

theorem val_gridUnit (s : Fin 4 → ℤ) (p B C q E r : ℤ) :
    ((gridUnit s p B C q E r : Matˣ) : Mat) = twoDiag s * uni p B C q E r :=
  rfl

theorem val_inv_gridUnit (s : Fin 4 → ℤ) (p B C q E r : ℤ) :
    (((gridUnit s p B C q E r)⁻¹ : Matˣ) : Mat) = uniInv p B C q E r * twoDiag (-s) :=
  rfl

theorem isGridPoint_gridUnit (s : Fin 4 → ℤ) (p B C q E r : ℤ) :
    IsGridPoint (gridUnit s p B C q E r) :=
  ⟨s, uniUnit p B C q E r, isIntegralUnitriangular_uniUnit p B C q E r, rfl⟩

/-- **Grid approximation**: every `γ ∈ GL₄(ℚ)` lies within bounded distance of a
dyadic grid point of the Borel subgroup. -/
theorem exists_gridPoint_near : ∃ c : ℚ, ∀ γ : ExplicitLinearModel.Matˣ, ∃ b : ExplicitLinearModel.Matˣ, IsGridPoint b ∧
    ∀ i j, |((b⁻¹ * γ : ExplicitLinearModel.Matˣ) : ExplicitLinearModel.Mat) i j| ≤ c ∧ |((γ⁻¹ * b : ExplicitLinearModel.Matˣ) : ExplicitLinearModel.Mat) i j| ≤ c := by
  refine ⟨16, fun γ => ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, hA⟩ := gs_eq (γ : Mat)
  obtain ⟨s, z, zt, hY, hmul, hzb, hztb⟩ := exists_dyadic_scaling (gsY_self_pos γ) (gsY_orth γ)
  obtain ⟨V, hV, hVup, hVd⟩ := uni_mul_twoDiag a0 a1 a2 a3 a4 a5 s
  obtain ⟨p, B, C, q, E, r, x0, x1, x2, x3, x4, x5, hround, h0, h1, h2, h3, h4, h5⟩ :=
    uni_round (V 0 1) (V 0 2) (V 0 3) (V 1 2) (V 1 3) (V 2 3)
  have hVeq : V = uni p B C q E r * uni x0 x1 x2 x3 x4 x5 :=
    (eq_uni_of_unitriangular hVup hVd).trans hround
  have hγ : (γ : Mat) = twoDiag s * uni p B C q E r * (uni x0 x1 x2 x3 x4 x5 * z) :=
    calc (γ : Mat) = uni a0 a1 a2 a3 a4 a5 * twoDiag s * z := by rw [mul_assoc, ← hY, ← hA]
      _ = twoDiag s * V * z := by rw [hV]
      _ = twoDiag s * uni p B C q E r * (uni x0 x1 x2 x3 x4 x5 * z) := by
          rw [hVeq]
          simp only [mul_assoc]
  have hγinv : ((γ⁻¹ : Matˣ) : Mat) =
      zt * uniInv x0 x1 x2 x3 x4 x5 * uniInv p B C q E r * twoDiag (-s) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hγ]
    simp only [mul_assoc]
    rw [← mul_assoc z, hmul, one_mul, ← mul_assoc (uni x0 x1 x2 x3 x4 x5), uni_mul_uniInv,
      one_mul, ← mul_assoc (uni p B C q E r), uni_mul_uniInv, one_mul, twoDiag_mul_twoDiag_neg]
  have hleft : (((gridUnit s p B C q E r)⁻¹ * γ : Matˣ) : Mat) =
      uni x0 x1 x2 x3 x4 x5 * z := by
    rw [Units.val_mul, val_inv_gridUnit, hγ]
    simp only [mul_assoc]
    rw [← mul_assoc (twoDiag (-s)), twoDiag_mul, neg_add_cancel, twoDiag_zero, one_mul,
      ← mul_assoc (uniInv p B C q E r), uniInv_mul_uni, one_mul]
  have hright : ((γ⁻¹ * gridUnit s p B C q E r : Matˣ) : Mat) =
      zt * uniInv x0 x1 x2 x3 x4 x5 := by
    rw [Units.val_mul, hγinv, val_gridUnit]
    simp only [mul_assoc]
    rw [← mul_assoc (twoDiag (-s)), twoDiag_mul, neg_add_cancel, twoDiag_zero, one_mul,
      uniInv_mul_uni, mul_one]
  have hg : ∀ i j, |uni x0 x1 x2 x3 x4 x5 i j| ≤ 2 := fun i j =>
    (abs_uni_frac_le h0 h1 h2 h3 h4 h5 i j).1
  have hginv : ∀ i j, |uniInv x0 x1 x2 x3 x4 x5 i j| ≤ 2 := fun i j =>
    (abs_uni_frac_le h0 h1 h2 h3 h4 h5 i j).2
  have h16 : (4 : ℚ) * (2 * 2) ≤ 16 := by norm_num
  refine ⟨gridUnit s p B C q E r, isGridPoint_gridUnit s p B C q E r, fun i j => ⟨?_, ?_⟩⟩
  · rw [hleft]
    exact (abs_mul_apply_le_of_bound hg hzb i j).trans h16
  · rw [hright]
    exact (abs_mul_apply_le_of_bound hztb hginv i j).trans h16

end GroupApproximation.Full.NN09b
