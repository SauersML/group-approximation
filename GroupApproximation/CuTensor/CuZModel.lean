import GroupApproximation.CuTensor.WayBelow
import Mathlib.Data.ENNReal.Basic

/-!
# The model `ℕ ⊔ (0, ∞]` of `Cu(𝒵)`

The Cuntz semigroup of the Jiang--Su algebra `𝒵` is the ordered monoid `ℕ ⊔ (0, ∞]`.  The
compact part `ℕ` holds the classes of projections, counted by their trace.  The soft part
`(0, ∞]` holds the remaining classes, counted by their rank.  A compact `n` lies below a soft `t`
exactly when `n < t`, and a soft `t` lies below a compact `n` exactly when `t ≤ n`.

This file builds that ordered monoid, `CuZModel`, as an inductive type with a compact and a soft
constructor.  It is not a computation of `Cu(𝒵)`: no operator algebra appears here.  It is the
target against which a statement `Cu(A) ≅ Cu(𝒵)` is measured, and it records the order-theoretic
fact that the counterexample to the first part of STW Problem XCV turns on.  The model is totally
ordered, so an ordered set with two incomparable elements is not order-isomorphic to it
(`not_nonempty_orderIso_cuZModel`).  In `Cu(E ⊗ E)` for the witness `E` of the research node
`stw95-cu-z-tensor-counterexample`, the classes of the trivial and the Bott projection have equal
trace and different `K₀` classes, so they are incomparable; producing those two classes, and the
isomorphism `Cu(E) ≅ Cu(𝒵)`, is the operator-algebraic part that this file does not touch.

## Main results

* `CuZModel`, with `instPartialOrder` and `instAddCommMonoid`;
* `CuZModel.le_total'`: the model is totally ordered;
* `CuZModel.not_nonempty_orderIso_cuZModel`: the obstruction.
-/

open scoped ENNReal

namespace GroupApproximation
namespace CuTensor

/-- The model `ℕ ⊔ (0, ∞]` of the Cuntz semigroup of the Jiang--Su algebra. -/
inductive CuZModel : Type
  /-- A compact class, the class of a projection of trace `n`. -/
  | cpt : ℕ → CuZModel
  /-- A soft class of rank `t ∈ (0, ∞]`. -/
  | soft (t : ℝ≥0∞) (ht : 0 < t) : CuZModel

namespace CuZModel

/-- The order of the model: compacts and softs are ordered by their values, except that a
compact `n` lies below a soft `t` only when `n < t`. -/
protected def le : CuZModel → CuZModel → Prop
  | cpt m, cpt n => m ≤ n
  | cpt m, soft t _ => (m : ℝ≥0∞) < t
  | soft s _, cpt n => s ≤ n
  | soft s _, soft t _ => s ≤ t

theorem le_refl' : ∀ a : CuZModel, CuZModel.le a a
  | cpt n => Nat.le_refl n
  | soft t _ => le_refl t

theorem le_trans' :
    ∀ a b c : CuZModel, CuZModel.le a b → CuZModel.le b c → CuZModel.le a c
  | cpt m, cpt n, cpt k, h₁, h₂ => Nat.le_trans h₁ h₂
  | cpt m, cpt n, soft t _, h₁, h₂ => by
      have h₂' : (n : ℝ≥0∞) < t := h₂
      show (m : ℝ≥0∞) < t
      exact lt_of_le_of_lt (Nat.cast_le.2 h₁) h₂'
  | cpt m, soft s _, cpt k, h₁, h₂ => by
      have h₁' : (m : ℝ≥0∞) < s := h₁
      have h₂' : s ≤ (k : ℝ≥0∞) := h₂
      show m ≤ k
      exact Nat.cast_le.1 (le_of_lt (lt_of_lt_of_le h₁' h₂'))
  | cpt m, soft s _, soft t _, h₁, h₂ => by
      have h₁' : (m : ℝ≥0∞) < s := h₁
      have h₂' : s ≤ t := h₂
      show (m : ℝ≥0∞) < t
      exact lt_of_lt_of_le h₁' h₂'
  | soft s _, cpt n, cpt k, h₁, h₂ => by
      have h₁' : s ≤ (n : ℝ≥0∞) := h₁
      have h₂' : n ≤ k := h₂
      show s ≤ (k : ℝ≥0∞)
      exact le_trans h₁' (Nat.cast_le.2 h₂')
  | soft s _, cpt n, soft t _, h₁, h₂ => by
      have h₁' : s ≤ (n : ℝ≥0∞) := h₁
      have h₂' : (n : ℝ≥0∞) < t := h₂
      show s ≤ t
      exact le_of_lt (lt_of_le_of_lt h₁' h₂')
  | soft s _, soft t _, cpt k, h₁, h₂ => by
      have h₁' : s ≤ t := h₁
      have h₂' : t ≤ (k : ℝ≥0∞) := h₂
      show s ≤ (k : ℝ≥0∞)
      exact le_trans h₁' h₂'
  | soft s _, soft t _, soft u _, h₁, h₂ => by
      have h₁' : s ≤ t := h₁
      have h₂' : t ≤ u := h₂
      show s ≤ u
      exact le_trans h₁' h₂'

theorem le_antisymm' : ∀ a b : CuZModel, CuZModel.le a b → CuZModel.le b a → a = b
  | cpt m, cpt n, h₁, h₂ => congrArg cpt (Nat.le_antisymm h₁ h₂)
  | cpt m, soft t _, h₁, h₂ => by
      have h₁' : (m : ℝ≥0∞) < t := h₁
      have h₂' : t ≤ (m : ℝ≥0∞) := h₂
      exact absurd (lt_of_lt_of_le h₁' h₂') (lt_irrefl _)
  | soft s _, cpt n, h₁, h₂ => by
      have h₁' : s ≤ (n : ℝ≥0∞) := h₁
      have h₂' : (n : ℝ≥0∞) < s := h₂
      exact absurd (lt_of_le_of_lt h₁' h₂') (lt_irrefl _)
  | soft s _, soft t _, h₁, h₂ => by
      have h₁' : s ≤ t := h₁
      have h₂' : t ≤ s := h₂
      obtain rfl : s = t := le_antisymm h₁' h₂'
      rfl

instance instPartialOrder : PartialOrder CuZModel where
  le := CuZModel.le
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'

@[simp] theorem cpt_le_cpt {m n : ℕ} : cpt m ≤ cpt n ↔ m ≤ n := Iff.rfl

@[simp] theorem cpt_le_soft {m : ℕ} {t : ℝ≥0∞} {ht : 0 < t} :
    cpt m ≤ soft t ht ↔ (m : ℝ≥0∞) < t := Iff.rfl

@[simp] theorem soft_le_cpt {s : ℝ≥0∞} {hs : 0 < s} {n : ℕ} :
    soft s hs ≤ cpt n ↔ s ≤ (n : ℝ≥0∞) := Iff.rfl

@[simp] theorem soft_le_soft {s t : ℝ≥0∞} {hs : 0 < s} {ht : 0 < t} :
    soft s hs ≤ soft t ht ↔ s ≤ t := Iff.rfl

/-- **The model is totally ordered.** -/
theorem le_total' : ∀ a b : CuZModel, a ≤ b ∨ b ≤ a
  | cpt m, cpt n => by
      show m ≤ n ∨ n ≤ m
      exact Nat.le_total m n
  | cpt m, soft t _ => by
      show (m : ℝ≥0∞) < t ∨ t ≤ (m : ℝ≥0∞)
      exact lt_or_ge _ _
  | soft s _, cpt n => by
      show s ≤ (n : ℝ≥0∞) ∨ (n : ℝ≥0∞) < s
      exact le_or_gt _ _
  | soft s _, soft t _ => by
      show s ≤ t ∨ t ≤ s
      exact le_total s t

/-- **The obstruction.** An ordered set with two incomparable elements is not order-isomorphic
to the model of `Cu(𝒵)`. -/
theorem not_nonempty_orderIso_cuZModel {α : Type*} [Preorder α] {a b : α} (hab : ¬ a ≤ b)
    (hba : ¬ b ≤ a) : ¬ Nonempty (α ≃o CuZModel) :=
  not_nonempty_orderIso_of_incomparable le_total' hab hba

/-- Addition in the model: values add, and a sum with a soft summand is soft. -/
protected def add : CuZModel → CuZModel → CuZModel
  | cpt m, cpt n => cpt (m + n)
  | cpt m, soft t ht => soft ((m : ℝ≥0∞) + t) (lt_of_lt_of_le ht le_add_self)
  | soft s hs, cpt n => soft (s + (n : ℝ≥0∞)) (lt_of_lt_of_le hs le_self_add)
  | soft s hs, soft t _ => soft (s + t) (lt_of_lt_of_le hs le_self_add)

instance : Zero CuZModel := ⟨cpt 0⟩

instance : Add CuZModel := ⟨CuZModel.add⟩

@[simp] theorem zero_def : (0 : CuZModel) = cpt 0 := rfl

@[simp] theorem cpt_add_cpt (m n : ℕ) : cpt m + cpt n = cpt (m + n) := rfl

@[simp] theorem cpt_add_soft (m : ℕ) (t : ℝ≥0∞) (ht : 0 < t) :
    cpt m + soft t ht = soft ((m : ℝ≥0∞) + t) (lt_of_lt_of_le ht le_add_self) := rfl

@[simp] theorem soft_add_cpt (s : ℝ≥0∞) (hs : 0 < s) (n : ℕ) :
    soft s hs + cpt n = soft (s + (n : ℝ≥0∞)) (lt_of_lt_of_le hs le_self_add) := rfl

@[simp] theorem soft_add_soft (s t : ℝ≥0∞) (hs : 0 < s) (ht : 0 < t) :
    soft s hs + soft t ht = soft (s + t) (lt_of_lt_of_le hs le_self_add) := rfl

theorem add_assoc' : ∀ a b c : CuZModel, a + b + c = a + (b + c) := by
  rintro (m | ⟨s, hs⟩) (n | ⟨t, ht⟩) (k | ⟨u, hu⟩) <;> simp [add_assoc]

theorem zero_add' : ∀ a : CuZModel, 0 + a = a := by
  rintro (n | ⟨t, ht⟩) <;> simp

theorem add_zero' : ∀ a : CuZModel, a + 0 = a := by
  rintro (n | ⟨t, ht⟩) <;> simp

theorem add_comm' : ∀ a b : CuZModel, a + b = b + a := by
  rintro (m | ⟨s, hs⟩) (n | ⟨t, ht⟩) <;> simp [add_comm]

instance instAddCommMonoid : AddCommMonoid CuZModel where
  add := (· + ·)
  zero := 0
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  nsmul := nsmulRec

end CuZModel

end CuTensor
end GroupApproximation
