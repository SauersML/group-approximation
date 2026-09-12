import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.Star.Unitary

/-!
# Faithful tracial states and C⋆-finiteness

This file isolates the C⋆-algebraic argument used in the manuscript's
stable-finiteness lemma.  The conclusion is the operator-algebraic assertion
that every isometry is unitary, rather than an algebraic stable-finiteness
typeclass.
-/

open scoped ComplexOrder

namespace GroupApproximation

noncomputable section

/-- A faithful tracial state on a unital complex C⋆-algebra.

Positivity is stated on elements of the form `x⋆ * x`, which is equivalent to
the usual positivity condition for linear functionals on a C⋆-algebra.
Faithfulness is stated in the form used by the finiteness argument. -/
structure FaithfulTracialState (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  map_one : toLinearMap 1 = 1
  map_star_mul_self_nonneg : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  map_mul_comm : ∀ x y : A, toLinearMap (x * y) = toLinearMap (y * x)
  eq_zero_of_map_star_mul_self_eq_zero :
    ∀ {x : A}, toLinearMap (star x * x) = 0 → x = 0

namespace FaithfulTracialState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

instance : CoeFun (FaithfulTracialState A) fun _ ↦ A → ℂ :=
  ⟨fun τ ↦ τ.toLinearMap⟩

@[simp]
theorem map_zero (τ : FaithfulTracialState A) : τ 0 = 0 :=
  τ.toLinearMap.map_zero

@[simp]
theorem map_add (τ : FaithfulTracialState A) (x y : A) : τ (x + y) = τ x + τ y :=
  τ.toLinearMap.map_add x y

@[simp]
theorem map_sub (τ : FaithfulTracialState A) (x y : A) : τ (x - y) = τ x - τ y :=
  τ.toLinearMap.map_sub x y

@[simp]
theorem map_smul (τ : FaithfulTracialState A) (c : ℂ) (x : A) : τ (c • x) = c • τ x :=
  τ.toLinearMap.map_smul c x

@[simp]
theorem apply_one (τ : FaithfulTracialState A) : τ 1 = 1 :=
  τ.map_one

/-- A faithful tracial state detects zero elements through `x⋆ * x`. -/
theorem map_star_mul_self_eq_zero_iff (τ : FaithfulTracialState A) (x : A) :
    τ (star x * x) = 0 ↔ x = 0 := by
  constructor
  · exact τ.eq_zero_of_map_star_mul_self_eq_zero
  · rintro rfl
    simp

/-- In a unital C⋆-algebra with a faithful tracial state, a left-unitary
element is also right-unitary.  Equivalently, every isometry is unitary. -/
theorem mul_star_eq_one_of_star_mul_eq_one (τ : FaithfulTracialState A) {v : A}
    (hv : star v * v = 1) : v * star v = 1 := by
  let p : A := 1 - v * star v
  have hp_star : star p = p := by
    simp [p]
  have hq_idem : (v * star v) * (v * star v) = v * star v := by
    calc
      (v * star v) * (v * star v) = v * (star v * v) * star v := by
        simp only [mul_assoc]
      _ = v * star v := by rw [hv, mul_one]
  have hp_idem : p * p = p := by
    dsimp [p]
    simp only [sub_mul, one_mul, mul_sub, mul_one, hq_idem, sub_self, sub_zero]
  have hτp : τ p = 0 := by
    dsimp [p]
    rw [map_sub, apply_one, τ.map_mul_comm v (star v), hv, apply_one, sub_self]
  have hp_zero : p = 0 := by
    apply τ.eq_zero_of_map_star_mul_self_eq_zero
    rw [hp_star, hp_idem, hτp]
  exact (sub_eq_zero.mp hp_zero).symm

/-- Membership formulation: every isometry belongs to the unitary group. -/
theorem mem_unitary_of_star_mul_eq_one (τ : FaithfulTracialState A) {v : A}
    (hv : star v * v = 1) : v ∈ unitary A := by
  rw [Unitary.mem_iff]
  exact ⟨hv, τ.mul_star_eq_one_of_star_mul_eq_one hv⟩

end FaithfulTracialState

end

end GroupApproximation
