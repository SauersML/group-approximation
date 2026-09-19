import GroupApproximation.Analysis.CStarExactness
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The sesquilinear form of a completely positive map

## What this module proves

`CStarExactness.IsCompletelyPositive` spells complete positivity through
matrices: positive matrices over the source map to positive matrices over
the target.  Every dilation argument -- Stinespring's construction in
particular -- consumes complete positivity in a different, equivalent shape:
**form positivity**.  For a completely positive `φ : A →ₗ[ℂ] (H →L[ℂ] H)`,
finitely many `a i : A` and vectors `h i : H`,

  `0 ≤ (∑ i, ∑ j, ⟪h i, φ (star (a i) * a j) (h j)⟫).re`  (and `.im = 0`).

This module proves that bridge:

* `star_col_mul_col` -- the matrix `(star (a i) * a j)ᵢⱼ` is `star N * N`
  for the matrix `N` carrying the tuple `a` in its first row;
* `sum_inner_star_mul_self` -- for a matrix of the form `star P * P` over
  `H →L[ℂ] H`, the associated form is `∑ k ‖∑ j, P k j (h j)‖²`, so it is
  real and nonnegative;
* `IsCompletelyPositive.form_nonneg` -- the two combined.

The Stinespring dilation space is the completion of `A ⊗ H` under exactly
this form; that construction is a later module.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05` remains
**MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset

universe u w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## Matrix entries

`CStarMatrix` differs from `Matrix` only in its norm, so entries of products
and stars are computed by the `Matrix` lemmas after a change of view. -/

theorem cstarMatrix_mul_apply {n : ℕ} {X : Type*} [NonUnitalCStarAlgebra X]
    (P Q : CStarMatrix (Fin n) (Fin n) X) (i j : Fin n) :
    (P * Q) i j = ∑ k, P i k * Q k j :=
  Matrix.mul_apply

@[simp] theorem cstarMatrix_star_apply {n : ℕ} {X : Type*} [NonUnitalCStarAlgebra X]
    (P : CStarMatrix (Fin n) (Fin n) X) (i j : Fin n) :
    (star P) i j = star (P j i) :=
  rfl

/-! ## The column trick -/

/-- The matrix `(star (a i) * a j)ᵢⱼ` is `star N * N` for the matrix `N`
whose first row is the tuple `a` and whose other rows vanish. -/
theorem star_col_mul_col {n : ℕ} [NeZero n] (a : Fin n → A) :
    ∃ N : CStarMatrix (Fin n) (Fin n) A,
      (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j))
        = star N * N := by
  refine ⟨CStarMatrix.ofMatrix
    (Matrix.of fun i j => if i = 0 then a j else 0), ?_⟩
  ext i j
  rw [cstarMatrix_mul_apply]
  show star (a i) * a j
      = ∑ k, (star (CStarMatrix.ofMatrix
            (Matrix.of fun i j => if i = 0 then a j else 0))) i k
          * (CStarMatrix.ofMatrix
            (Matrix.of fun i j => if i = 0 then a j else 0)) k j
  rw [Finset.sum_eq_single (0 : Fin n)]
  · show star (a i) * a j
        = star (if (0 : Fin n) = 0 then a i else 0)
          * (if (0 : Fin n) = 0 then a j else 0)
    rw [if_pos rfl, if_pos rfl]
  · intro k _ hk
    show star (if k = 0 then a i else 0) * (if k = 0 then a j else 0) = 0
    rw [if_neg hk, if_neg hk, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Positivity of the form of a `star P * P` matrix -/

/-- For a matrix of the form `star P * P` over the bounded operators, the
associated sesquilinear sum is a sum of squared norms. -/
theorem sum_inner_star_mul_self {n : ℕ}
    (P : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) (h : Fin n → H) :
    (∑ i, ∑ j, ⟪h i, (star P * P) i j (h j)⟫_ℂ)
      = ∑ k, ((‖∑ j, P k j (h j)‖ : ℝ) : ℂ) ^ 2 := by
  calc (∑ i, ∑ j, ⟪h i, (star P * P) i j (h j)⟫_ℂ)
      = ∑ i, ∑ j, ∑ k, ⟪P k i (h i), P k j (h j)⟫_ℂ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        show ⟪h i, (∑ k, star (P k i) * P k j) (h j)⟫_ℂ = _
        rw [_root_.sum_apply, inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        show ⟪h i, (star (P k i)) ((P k j) (h j))⟫_ℂ = _
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
    _ = ∑ k, ∑ i, ∑ j, ⟪P k i (h i), P k j (h j)⟫_ℂ := by
        have h1 : ∀ i : Fin n,
            (∑ j, ∑ k, ⟪P k i (h i), P k j (h j)⟫_ℂ)
              = ∑ k, ∑ j, ⟪P k i (h i), P k j (h j)⟫_ℂ :=
          fun i => Finset.sum_comm
        rw [Finset.sum_congr rfl fun i _ => h1 i]
        exact Finset.sum_comm
    _ = ∑ k, ⟪∑ i, P k i (h i), ∑ j, P k j (h j)⟫_ℂ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_sum]
    _ = ∑ k, ((‖∑ j, P k j (h j)‖ : ℝ) : ℂ) ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact inner_self_eq_norm_sq_to_K _

/-! ## The bridge -/

/-- **Form positivity of a completely positive map**: the sesquilinear sum
`∑ᵢⱼ ⟪h i, φ (star (a i) * a j) (h j)⟫` is real and nonnegative.  This is
the shape of complete positivity every dilation argument consumes. -/
theorem IsCompletelyPositive.form_nonneg {φ : A →ₗ[ℂ] (H →L[ℂ] H)}
    (hφ : IsCompletelyPositive φ) {n : ℕ} [NeZero n]
    (a : Fin n → A) (h : Fin n → H) :
    0 ≤ (∑ i, ∑ j, ⟪h i, φ (star (a i) * a j) (h j)⟫_ℂ).re ∧
      (∑ i, ∑ j, ⟪h i, φ (star (a i) * a j) (h j)⟫_ℂ).im = 0 := by
  obtain ⟨N, hN⟩ := star_col_mul_col a
  obtain ⟨P, hP⟩ :=
    hφ n (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j))
      ⟨N, hN⟩
  have hφa : ∀ i j, φ (star (a i) * a j) = (star P * P) i j := by
    intro i j
    exact congrArg (fun M => M i j) hP
  have hsum : (∑ i, ∑ j, ⟪h i, φ (star (a i) * a j) (h j)⟫_ℂ)
      = ∑ k, ((‖∑ j, P k j (h j)‖ : ℝ) : ℂ) ^ 2 := by
    rw [← sum_inner_star_mul_self P h]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφa]
  have hterm : ∀ r : ℝ, (((r : ℝ) : ℂ) ^ 2)
      = (((r ^ 2 : ℝ)) : ℂ) := by
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

end CStarExactness
end GroupApproximation
