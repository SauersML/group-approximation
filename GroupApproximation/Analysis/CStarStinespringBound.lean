import GroupApproximation.Analysis.CStarStinespringForm

/-!
# The weighted form of a completely positive map

## What this module proves

The boundedness of the Stinespring representation rests on one
inequality: for a completely positive `φ`, tuples `a`, vectors `h`, and
any element whose defect `star d * d` majorizes the multiplier, the
weighted sesquilinear sum

  `∑ᵢⱼ ⟪h i, φ (star (a i) * (star d * d) * a j) (h j)⟫`

is real and nonnegative.  This module proves exactly that, by the
weighted column trick: the matrix `(star (a i) * (star d * d) * a j)ᵢⱼ`
is `star N * N` for the matrix `N` whose first row is `(d * a j)ⱼ`, so
complete positivity applies to it just as it does to the unweighted
Gram matrix.

* `star_col_mid_mul_col` -- the weighted column trick;
* `IsCompletelyPositive.form_nonneg_middle` -- the weighted form
  positivity over `Fin n`;
* `IsCompletelyPositive.form_nonneg_middle_finset` -- the same over a
  finset, the index shape the dilation pre-space consumes.

The decomposition `‖c‖² • 1 - star c * c = star d * d` that feeds `d`
is order theory and lives with the representation module, not here;
this module is pure matrix algebra over the predicate.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset

universe u w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The weighted column trick**: the matrix
`(star (a i) * (star d * d) * a j)ᵢⱼ` is `star N * N` for the matrix `N`
whose first row is `(d * a j)ⱼ` and whose other rows vanish. -/
theorem star_col_mid_mul_col {n : ℕ} [NeZero n] (a : Fin n → A) (d : A) :
    ∃ N : CStarMatrix (Fin n) (Fin n) A,
      (CStarMatrix.ofMatrix
          (Matrix.of fun i j => star (a i) * (star d * d) * a j))
        = star N * N := by
  refine ⟨CStarMatrix.ofMatrix
    (Matrix.of fun i j => if i = 0 then d * a j else 0), ?_⟩
  ext i j
  rw [cstarMatrix_mul_apply]
  show star (a i) * (star d * d) * a j
      = ∑ k, (star (CStarMatrix.ofMatrix
            (Matrix.of fun i j => if i = 0 then d * a j else 0))) i k
          * (CStarMatrix.ofMatrix
            (Matrix.of fun i j => if i = 0 then d * a j else 0)) k j
  rw [Finset.sum_eq_single (0 : Fin n)]
  · show star (a i) * (star d * d) * a j
        = star (if (0 : Fin n) = 0 then d * a i else 0)
          * (if (0 : Fin n) = 0 then d * a j else 0)
    rw [if_pos rfl, if_pos rfl]
    simp [star_mul, mul_assoc]
  · intro k _ hk
    show star (if k = 0 then d * a i else 0) * (if k = 0 then d * a j else 0)
        = 0
    rw [if_neg hk, if_neg hk, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Weighted form positivity** of a completely positive map. -/
theorem IsCompletelyPositive.form_nonneg_middle
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ) {n : ℕ}
    [NeZero n] (a : Fin n → A) (d : A) (h : Fin n → H) :
    0 ≤ (∑ i, ∑ j,
        ⟪h i, φ (star (a i) * (star d * d) * a j) (h j)⟫_ℂ).re ∧
      (∑ i, ∑ j,
        ⟪h i, φ (star (a i) * (star d * d) * a j) (h j)⟫_ℂ).im = 0 := by
  obtain ⟨N, hN⟩ := star_col_mid_mul_col a d
  obtain ⟨P, hP⟩ :=
    hφ n (CStarMatrix.ofMatrix
      (Matrix.of fun i j => star (a i) * (star d * d) * a j)) ⟨N, hN⟩
  have hφa : ∀ i j, φ (star (a i) * (star d * d) * a j) = (star P * P) i j :=
    fun i j => congrArg (fun M => M i j) hP
  have hsum : (∑ i, ∑ j,
      ⟪h i, φ (star (a i) * (star d * d) * a j) (h j)⟫_ℂ)
      = ∑ k, ((‖∑ j, P k j (h j)‖ : ℝ) : ℂ) ^ 2 := by
    rw [← sum_inner_star_mul_self P h]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφa]
  have hterm : ∀ r : ℝ, (((r : ℝ) : ℂ) ^ 2) = (((r ^ 2 : ℝ)) : ℂ) := by
    intro r
    push_cast
    ring
  have hre : (∑ k, ((‖∑ j, P k j (h j)‖ : ℝ) : ℂ) ^ 2).re
      = ∑ k, ‖∑ j, P k j (h j)‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun k _ => hterm ‖∑ j, P k j (h j)‖]
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_re _
  have him : (∑ k, ((‖∑ j, P k j (h j)‖ : ℝ) : ℂ) ^ 2).im = 0 := by
    rw [Finset.sum_congr rfl fun k _ => hterm ‖∑ j, P k j (h j)‖]
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_im _
  constructor
  · rw [hsum, hre]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  · rw [hsum, him]

/-- **Weighted form positivity over a finset**, the index shape the
dilation pre-space consumes. -/
theorem IsCompletelyPositive.form_nonneg_middle_finset
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ)
    (s : Finset A) (d : A) (k : A → H) :
    0 ≤ (∑ a ∈ s, ∑ b ∈ s,
        ⟪k a, φ (star a * (star d * d) * b) (k b)⟫_ℂ).re ∧
      (∑ a ∈ s, ∑ b ∈ s,
        ⟪k a, φ (star a * (star d * d) * b) (k b)⟫_ℂ).im = 0 := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simp
  · haveI : NeZero s.card := ⟨(Finset.card_pos.mpr hs).ne'⟩
    have h := hφ.form_nonneg_middle (φ := φ) (n := s.card)
      (fun i => ((s.equivFin.symm i : A))) d
      (fun i => k ((s.equivFin.symm i : A)))
    rw [double_sum_equivFin s
      (fun a b => ⟪k a, φ (star a * (star d * d) * b) (k b)⟫_ℂ)]
    exact h

end CStarExactness
end GroupApproximation
