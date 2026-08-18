import GroupApproximation.Analysis.CStarCompletelyPositiveStar

/-!
# Form positivity over finite sets: the Stinespring index bridge

## What this module proves

`CStarCompletelyPositiveForm.IsCompletelyPositive.form_nonneg` states form
positivity over tuples indexed by `Fin n`.  The Stinespring pre-space is a
finitely supported function space, whose sesquilinear form sums over
*finsets* of algebra elements; this module transports positivity to that
index shape:

  `0 ≤ (∑ a ∈ s, ∑ b ∈ s, ⟪k a, φ (star a * b) (k b)⟫).re`  (and `.im = 0`)

for every finset `s` and every assignment `k` of vectors.  The transport is
the equivalence `s ≃ Fin s.card`, applied to both sums, with the empty case
read off directly.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05` remains
**MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

universe u w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [NonUnitalCStarAlgebra A] in
/-- Reindex a finset double sum through `s.equivFin`. -/
theorem double_sum_equivFin (s : Finset A) (F : A → A → ℂ) :
    (∑ a ∈ s, ∑ b ∈ s, F a b)
      = ∑ i : Fin s.card, ∑ j : Fin s.card,
          F ((s.equivFin.symm i : A)) ((s.equivFin.symm j : A)) := by
  classical
  have h1 : (∑ a ∈ s, ∑ b ∈ s, F a b)
      = ∑ x : ↥s, ∑ y : ↥s, F (x : A) (y : A) := by
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_coe_sort s]
  rw [h1]
  rw [← Equiv.sum_comp s.equivFin.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp s.equivFin.symm]

/-- **Form positivity over a finset**: the finset-indexed sesquilinear sum
of a completely positive map is real and nonnegative. -/
theorem IsCompletelyPositive.form_nonneg_finset
    {φ : A →ₗ[ℂ] (H →L[ℂ] H)} (hφ : IsCompletelyPositive φ)
    (s : Finset A) (k : A → H) :
    0 ≤ (∑ a ∈ s, ∑ b ∈ s, ⟪k a, φ (star a * b) (k b)⟫_ℂ).re ∧
      (∑ a ∈ s, ∑ b ∈ s, ⟪k a, φ (star a * b) (k b)⟫_ℂ).im = 0 := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simp
  · haveI : NeZero s.card := ⟨(Finset.card_pos.mpr hs).ne'⟩
    have h := hφ.form_nonneg (φ := φ) (n := s.card)
      (fun i => ((s.equivFin.symm i : A)))
      (fun i => k ((s.equivFin.symm i : A)))
    rw [double_sum_equivFin s
      (fun a b => ⟪k a, φ (star a * b) (k b)⟫_ℂ)]
    exact h

end CStarExactness
end GroupApproximation
