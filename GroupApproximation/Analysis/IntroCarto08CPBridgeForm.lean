import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# The form of a `star P * P` block matrix over `M_Y`

This is infrastructure for lane `nm-intro-08`, the bridge from
`CStarExactness.IsCompletelyPositive` to the entrywise form predicate
`Quasidiagonal.IsCompletelyPositiveOnMatrices`.  The lane is part of the
Blackadar--Kirchberg chain of `non_mf_groups_exist.tex` (NF ⇒ quasidiagonal,
tex 310), where a completely positive `down` map from an NF approximation has
to feed a quasidiagonal model.

This module does no C⋆-algebra work.  It is pure matrix algebra over `ℂ`.
Suppose `F i j = ∑ₖ (P k i)ᴴ (P k j)` for matrices `P k i : M_Y`.  Then

`∑ᵢⱼ ∑ₓᵧ conj (w i x) · F i j x y · w j y = ∑ₖ ∑_z |∑ⱼ ∑ᵧ P k j z y · w j y|²`,

so the left side is real and nonnegative.  The proof expands the matrix
products, moves `k` and `z` to the front in two rotations, and recognises each
`(k, z)` slice as `conj u · u`.
-/

namespace GroupApproximation
namespace IntroCarto08

/-- Rotate three finite sums: the outermost index moves innermost. -/
theorem sum_three_rotate {σ τ υ : Type*} [Fintype σ] [Fintype τ] [Fintype υ]
    (g : σ → τ → υ → ℂ) :
    (∑ s : σ, ∑ t : τ, ∑ u : υ, g s t u) = ∑ t : τ, ∑ u : υ, ∑ s : σ, g s t u :=
  calc (∑ s : σ, ∑ t : τ, ∑ u : υ, g s t u)
      = ∑ t : τ, ∑ s : σ, ∑ u : υ, g s t u := Finset.sum_comm
    _ = ∑ t : τ, ∑ u : υ, ∑ s : σ, g s t u :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

#audit_axioms GroupApproximation.IntroCarto08.sum_three_rotate

/-- Move the last two of six finite sums to the front. -/
theorem sum_six_rotate {α β γ δ κ ρ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] [Fintype κ] [Fintype ρ]
    (f : α → β → γ → δ → κ → ρ → ℂ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ k : κ, ∑ z : ρ, f a b c d k z)
      = ∑ k : κ, ∑ z : ρ, ∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d k z :=
  calc (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ k : κ, ∑ z : ρ, f a b c d k z)
      = ∑ a : α, ∑ b : β, ∑ c : γ, ∑ k : κ, ∑ z : ρ, ∑ d : δ, f a b c d k z :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
          Finset.sum_congr rfl fun c _ ↦ sum_three_rotate (fun d k z ↦ f a b c d k z)
    _ = ∑ a : α, ∑ b : β, ∑ k : κ, ∑ z : ρ, ∑ c : γ, ∑ d : δ, f a b c d k z :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
          sum_three_rotate (fun c k z ↦ ∑ d : δ, f a b c d k z)
    _ = ∑ a : α, ∑ k : κ, ∑ z : ρ, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d k z :=
        Finset.sum_congr rfl fun a _ ↦
          sum_three_rotate (fun b k z ↦ ∑ c : γ, ∑ d : δ, f a b c d k z)
    _ = ∑ k : κ, ∑ z : ρ, ∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d k z :=
        sum_three_rotate (fun a k z ↦ ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d k z)

#audit_axioms GroupApproximation.IntroCarto08.sum_six_rotate

/-- **The form of a `star P * P` block matrix is a sum of squared moduli.** -/
theorem sum_form_eq_sum_normSq {Y : FiniteModel} {m : ℕ}
    (F P : Fin m → Fin m → Matrix Y Y ℂ)
    (hF : ∀ i j : Fin m, F i j = ∑ k : Fin m, star (P k i) * P k j)
    (w : Fin m → Y → ℂ) :
    (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * F i j x y * w j y)
      = ∑ k : Fin m, ∑ z : Y,
          ((Complex.normSq (∑ j : Fin m, ∑ y : Y, P k j z y * w j y) : ℝ) : ℂ) := by
  have hterm : ∀ (i j : Fin m) (x y : Y),
      (starRingEnd ℂ) (w i x) * F i j x y * w j y
        = ∑ k : Fin m, ∑ z : Y,
            (starRingEnd ℂ) (P k i z x * w i x) * (P k j z y * w j y) := by
    intro i j x y
    simp only [hF i j, Matrix.sum_apply, Matrix.mul_apply, Matrix.star_apply,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    simp only [starRingEnd_apply, star_mul']
    ring
  calc (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * F i j x y * w j y)
      = ∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y, ∑ k : Fin m, ∑ z : Y,
          (starRingEnd ℂ) (P k i z x * w i x) * (P k j z y * w j y) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦
            hterm i j x y
    _ = ∑ k : Fin m, ∑ z : Y, ∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
          (starRingEnd ℂ) (P k i z x * w i x) * (P k j z y * w j y) :=
        sum_six_rotate (fun i j x y k z ↦
          (starRingEnd ℂ) (P k i z x * w i x) * (P k j z y * w j y))
    _ = ∑ k : Fin m, ∑ z : Y,
          ((Complex.normSq (∑ j : Fin m, ∑ y : Y, P k j z y * w j y) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
        rw [Complex.normSq_eq_conj_mul_self]
        simp only [map_sum, Finset.sum_mul_sum]

#audit_axioms GroupApproximation.IntroCarto08.sum_form_eq_sum_normSq

/-- **The form of a `star P * P` block matrix is real and nonnegative**, in
exactly the shape of `Quasidiagonal.IsCompletelyPositiveOnMatrices`. -/
theorem form_im_eq_zero_and_re_nonneg {Y : FiniteModel} {m : ℕ}
    (F P : Fin m → Fin m → Matrix Y Y ℂ)
    (hF : ∀ i j : Fin m, F i j = ∑ k : Fin m, star (P k i) * P k j)
    (w : Fin m → Y → ℂ) :
    (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * F i j x y * w j y).im = 0
      ∧ 0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * F i j x y * w j y).re := by
  rw [sum_form_eq_sum_normSq F P hF w]
  have hcast : (∑ k : Fin m, ∑ z : Y,
        ((Complex.normSq (∑ j : Fin m, ∑ y : Y, P k j z y * w j y) : ℝ) : ℂ))
      = ((∑ k : Fin m, ∑ z : Y,
          Complex.normSq (∑ j : Fin m, ∑ y : Y, P k j z y * w j y) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ (Complex.ofReal_sum _ _).symm
  rw [hcast, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _⟩

#audit_axioms GroupApproximation.IntroCarto08.form_im_eq_zero_and_re_nonneg

end IntroCarto08
end GroupApproximation
