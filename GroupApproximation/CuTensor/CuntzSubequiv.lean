import Mathlib.Analysis.CStarAlgebra.Basic
import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann

/-!
# Cuntz subequivalence

For elements `a, b` of a C-star algebra, `a` is *Cuntz subequivalent* to `b` when `a` is a norm
limit of elements `r b r*`.  On positive elements of `A ⊗ 𝒦` this relation, and the equivalence
it generates, define the Cuntz semigroup `Cu(A)`.

This file defines the relation over a normed `*`-ring.  It proves that the relation is transitive
when the star is isometric and reflexive in the unital case.  It also proves that Murray--von
Neumann equivalence of projections and the order `p q = p` of projections both imply it.  These are
the elementary inputs for comparing projection classes inside `Cu(A)`.

The converse for projections, that Cuntz subequivalence `p ≾ q` makes `p` Murray--von Neumann
equivalent to a subprojection of `q`, needs functional calculus and is not proved here.

## Main results

* `CuntzLE`, `cuntzLE_of_eq`;
* `CuntzLE.trans`, `CuntzLE.refl`;
* `cuntzLE_of_murrayVonNeumannEquiv`, `cuntzLE_of_mul_eq`.
-/

namespace GroupApproximation
namespace CuTensor

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A]

/-- **Cuntz subequivalence.** `CuntzLE a b` says that `a` is a norm limit of elements
`r * b * star r`. -/
def CuntzLE (a b : A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : A, ‖r * b * star r - a‖ < ε

/-- An exact identity `r * b * star r = a` gives Cuntz subequivalence. -/
theorem cuntzLE_of_eq {a b : A} (r : A) (h : r * b * star r = a) : CuntzLE a b :=
  fun ε hε => ⟨r, by simpa [h] using hε⟩

/-- **Cuntz subequivalence is transitive** when the star is isometric. -/
theorem CuntzLE.trans [NormedStarGroup A] {a b c : A} (hab : CuntzLE a b) (hbc : CuntzLE b c) :
    CuntzLE a c := by
  intro ε hε
  obtain ⟨r, hr⟩ := hab (ε / 2) (half_pos hε)
  have hM : 0 < ‖r‖ * ‖r‖ + 1 := by positivity
  have hδ : 0 < ε / 2 / (‖r‖ * ‖r‖ + 1) := div_pos (half_pos hε) hM
  obtain ⟨s, hs⟩ := hbc _ hδ
  refine ⟨r * s, ?_⟩
  have key : r * s * c * star (r * s) - a =
      r * (s * c * star s - b) * star r + (r * b * star r - a) := by
    simp only [star_mul, mul_sub, sub_mul, mul_assoc]
    abel
  have hnorm : ‖r * (s * c * star s - b) * star r‖ ≤ ‖r‖ * ‖r‖ * ‖s * c * star s - b‖ := by
    calc ‖r * (s * c * star s - b) * star r‖
        ≤ ‖r * (s * c * star s - b)‖ * ‖star r‖ := norm_mul_le _ _
      _ ≤ ‖r‖ * ‖s * c * star s - b‖ * ‖star r‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖r‖ * ‖r‖ * ‖s * c * star s - b‖ := by rw [norm_star]; ring
  have hsmall : ‖r‖ * ‖r‖ * ‖s * c * star s - b‖ ≤ ε / 2 := by
    calc ‖r‖ * ‖r‖ * ‖s * c * star s - b‖
        ≤ (‖r‖ * ‖r‖ + 1) * ‖s * c * star s - b‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ (‖r‖ * ‖r‖ + 1) * (ε / 2 / (‖r‖ * ‖r‖ + 1)) :=
          mul_le_mul_of_nonneg_left hs.le hM.le
      _ = ε / 2 := mul_div_cancel₀ _ hM.ne'
  rw [key]
  have htri := norm_add_le (r * (s * c * star s - b) * star r) (r * b * star r - a)
  linarith

/-- **Murray--von Neumann equivalence implies Cuntz subequivalence.** If `v* v = p` and
`v v* = q` with `p` idempotent, then `v* q v = p`. -/
theorem cuntzLE_of_murrayVonNeumannEquiv {p q : A} (hp : IsIdempotentElem p)
    (h : MurrayVonNeumannEquiv p q) : CuntzLE p q := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine cuntzLE_of_eq (star v) ?_
  rw [star_star, ← hv₂]
  calc star v * (v * star v) * v = star v * v * (star v * v) := by simp only [mul_assoc]
    _ = p := by rw [hv₁, hp.eq]

/-- **A subprojection is Cuntz subequivalent.** If `p` is a projection with `p q = p`, then
`p q p* = p`. -/
theorem cuntzLE_of_mul_eq {p q : A} (hp : IsStarProjection p) (hpq : p * q = p) :
    CuntzLE p q := by
  refine cuntzLE_of_eq p ?_
  rw [hp.isSelfAdjoint.star_eq, hpq, hp.isIdempotentElem.eq]

end NonUnital

section Unital

variable {A : Type*} [NormedRing A] [StarRing A]

/-- **Cuntz subequivalence is reflexive** in a unital algebra. -/
theorem CuntzLE.refl (a : A) : CuntzLE a a :=
  cuntzLE_of_eq 1 (by rw [star_one, one_mul, mul_one])

end Unital

end CuTensor
end GroupApproximation
