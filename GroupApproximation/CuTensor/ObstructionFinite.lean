import GroupApproximation.CuTensor.ObstructionCuntzProjection

/-!
# Mutual Cuntz subequivalence of projections in a finite C-star algebra

In a finite unital C-star algebra, where every isometry is unitary, two projections that are
Cuntz subequivalent to each other are Murray--von Neumann equivalent.  This is the step that
makes the map from the Murray--von Neumann monoid of a stably finite algebra to its Cuntz semigroup
injective.

## The proof

By `exists_murrayVonNeumannEquiv_le_of_cuntzLE` there are projections `q' ≤ q` and `p' ≤ p` with
`p ∼ q'` via `w₁` and `q ∼ p'` via `w₂`.  The product `u = w₁ w₂` has `u* u = q`, and its range
projection `u u* = w₁ p' w₁*` lies below `q'`, hence below `q`.  Finiteness forces `u u* = q`
(`cstar_eq_of_murrayVonNeumannEquiv_of_absorbs`), so `q ≤ q' ≤ q` and `p ∼ q' = q`.

The partial isometry relations `v p = v` and `q v = v` for `v* v = p`, `v v* = q` come from the
C-star identity.

## Main results

* `mul_eq_of_star_mul_self_eq`, `mul_eq_of_mul_star_self_eq`, `isStarProjection_mul_star_self`;
* `murrayVonNeumannEquiv_of_le_of_le`: mutual Murray--von Neumann subequivalence gives equivalence;
* `murrayVonNeumannEquiv_of_cuntzLE_of_cuntzLE`: mutual Cuntz subequivalence gives equivalence.
-/

namespace GroupApproximation
namespace CuTensor

section CStar

variable {A : Type*} [CStarAlgebra A]

/-- **A Murray--von Neumann equivalence is implemented by a partial isometry.**  If `v* v = p` is a
projection, then `v p = v`. -/
theorem mul_eq_of_star_mul_self_eq {v p : A} (hp : IsStarProjection p) (hv : star v * v = p) :
    v * p = v := by
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hp2 : p * p = p := hp.isIdempotentElem.eq
  have hvv : ∀ y : A, star v * (v * y) = p * y := fun y => by rw [← mul_assoc, hv]
  have h0 : star (v - v * p) * (v - v * p) = 0 := by
    simp only [star_sub, star_mul, hps, sub_mul, mul_sub, mul_assoc, hv, hvv, hp2, sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp h0)).symm

/-- If `v v* = q` is a projection, then `q v = v`. -/
theorem mul_eq_of_mul_star_self_eq {v q : A} (hq : IsStarProjection q) (hv : v * star v = q) :
    q * v = v := by
  have h := mul_eq_of_star_mul_self_eq hq (v := star v) (by rw [star_star]; exact hv)
  have h' := congrArg star h
  rwa [star_mul, star_star, hq.isSelfAdjoint.star_eq] at h'

/-- If `u* u` is a projection, so is `u u*`. -/
theorem isStarProjection_mul_star_self {u q : A} (hq : IsStarProjection q)
    (hu : star u * u = q) : IsStarProjection (u * star u) where
  isIdempotentElem := by
    show u * star u * (u * star u) = u * star u
    rw [mul_assoc, ← mul_assoc (star u), hu, ← mul_assoc, mul_eq_of_star_mul_self_eq hq hu]
  isSelfAdjoint := by
    show star (u * star u) = u * star u
    rw [star_mul, star_star]

/-- **Mutual Murray--von Neumann subequivalence in a finite C-star algebra.**  If `p ∼ q'` with
`q' ≤ q` and `q ∼ p'` with `p' ≤ p`, and every isometry is unitary, then `p ∼ q`. -/
theorem murrayVonNeumannEquiv_of_le_of_le
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q p' q' : A} (hq : IsStarProjection q) (hp' : IsStarProjection p')
    (hq' : IsStarProjection q') (hpp' : p * p' = p') (hqq' : q * q' = q')
    (h₁ : MurrayVonNeumannEquiv p q') (h₂ : MurrayVonNeumannEquiv q p') :
    MurrayVonNeumannEquiv p q := by
  obtain ⟨w₁, hw₁p, hw₁q'⟩ := h₁
  obtain ⟨w₂, hw₂q, hw₂p'⟩ := h₂
  have hw₁l : q' * w₁ = w₁ := mul_eq_of_mul_star_self_eq hq' hw₁q'
  have hw₂l : p' * w₂ = w₂ := mul_eq_of_mul_star_self_eq hp' hw₂p'
  have hpw₂ : p * w₂ = w₂ := by rw [← hw₂l, ← mul_assoc, hpp']
  have hqw₁ : q * w₁ = w₁ := by rw [← hw₁l, ← mul_assoc, hqq']
  have hu1 : star (w₁ * w₂) * (w₁ * w₂) = q := by
    rw [star_mul, mul_assoc, ← mul_assoc (star w₁), hw₁p, hpw₂, hw₂q]
  have hqp'' : q * (w₁ * w₂ * star (w₁ * w₂)) = w₁ * w₂ * star (w₁ * w₂) := by
    rw [← mul_assoc, ← mul_assoc, hqw₁]
  have hp''q : w₁ * w₂ * star (w₁ * w₂) = q :=
    cstar_eq_of_murrayVonNeumannEquiv_of_absorbs hfinite (isStarProjection_mul_star_self hq hu1)
      hq hqp'' (MurrayVonNeumannEquiv.symm ⟨w₁ * w₂, hu1, rfl⟩)
  have hq'p'' : q' * (w₁ * w₂ * star (w₁ * w₂)) = w₁ * w₂ * star (w₁ * w₂) := by
    rw [← mul_assoc, ← mul_assoc, hw₁l]
  rw [hp''q] at hq'p''
  have hqq : q' = q := by
    have h1 : star (q * q') = star q' := congrArg star hqq'
    rw [star_mul, hq.isSelfAdjoint.star_eq, hq'.isSelfAdjoint.star_eq, hq'p''] at h1
    exact h1.symm
  exact ⟨w₁, hw₁p, hw₁q'.trans hqq⟩

end CStar

section Ordered

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Mutual Cuntz subequivalence of projections in a finite C-star algebra.**  If every isometry is
unitary, two projections that are Cuntz subequivalent to each other are Murray--von Neumann
equivalent. -/
theorem murrayVonNeumannEquiv_of_cuntzLE_of_cuntzLE
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : CuntzLE p q) (hqp : CuntzLE q p) : MurrayVonNeumannEquiv p q := by
  obtain ⟨q', hq', hqq', h₁⟩ := exists_murrayVonNeumannEquiv_le_of_cuntzLE hp hq hpq
  obtain ⟨p', hp', hpp', h₂⟩ := exists_murrayVonNeumannEquiv_le_of_cuntzLE hq hp hqp
  exact murrayVonNeumannEquiv_of_le_of_le hfinite hq hp' hq' hpp' hqq' h₁ h₂

end Ordered

end CuTensor
end GroupApproximation
