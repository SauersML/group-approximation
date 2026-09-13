import GroupApproximation.CuTensor.WayBelow
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Monotone.Basic

/-!
# The axioms of a Cu-semigroup

A Cu-semigroup is a positively ordered commutative monoid satisfying the sequential axioms
O1–O4 of Coward, Elliott and Ivanescu:

* (O1) every increasing sequence has a supremum;
* (O2) every element is the supremum of a rapidly increasing sequence `x₀ ≪ x₁ ≪ ⋯`;
* (O3) `x ≪ y` and `x' ≪ y'` imply `x + x' ≪ y + y'`;
* (O4) the supremum of a sum of increasing sequences is the sum of the suprema.

The relation `≪` is `GroupApproximation.CuTensor.WayBelow`, stated with increasing sequences.
This file also adds the two monotonicity lemmas for `WayBelow`.
-/

namespace GroupApproximation
namespace CuTensor

section WayBelowMono

variable {α : Type*} [Preorder α]

/-- `x ≤ y ≪ z` implies `x ≪ z`. -/
theorem WayBelow.of_le_left {x y z : α} (hxy : x ≤ y) (hyz : WayBelow y z) : WayBelow x z := by
  intro f hf s hs hzs
  obtain ⟨n, hn⟩ := hyz f hf s hs hzs
  exact ⟨n, le_trans hxy hn⟩

/-- `x ≪ y ≤ z` implies `x ≪ z`. -/
theorem WayBelow.of_le_right {x y z : α} (hxy : WayBelow x y) (hyz : y ≤ z) : WayBelow x z := by
  intro f hf s hs hzs
  exact hxy f hf s hs (le_trans hyz hzs)

/-- A rapidly increasing sequence is increasing. -/
theorem monotone_of_wayBelow_seq {f : ℕ → α} (hf : ∀ n, WayBelow (f n) (f (n + 1))) :
    Monotone f :=
  monotone_nat_of_le_succ fun n => (hf n).le

end WayBelowMono

/-- The axioms O1–O4 of a Cu-semigroup, for a partially ordered commutative monoid. -/
structure IsCuSemigroup (S : Type*) [PartialOrder S] [AddCommMonoid S] : Prop where
  /-- The order is positive. -/
  zero_le : ∀ x : S, 0 ≤ x
  /-- Addition is monotone. -/
  add_le_add : ∀ {x y x' y' : S}, x ≤ y → x' ≤ y' → x + x' ≤ y + y'
  /-- (O1) Increasing sequences have suprema. -/
  exists_isLUB : ∀ f : ℕ → S, Monotone f → ∃ s, IsLUB (Set.range f) s
  /-- (O2) Every element is the supremum of a rapidly increasing sequence. -/
  exists_wayBelow_seq : ∀ x : S, ∃ f : ℕ → S,
    (∀ n, WayBelow (f n) (f (n + 1))) ∧ IsLUB (Set.range f) x
  /-- (O3) `≪` is compatible with addition. -/
  wayBelow_add : ∀ {x y x' y' : S}, WayBelow x y → WayBelow x' y' →
    WayBelow (x + x') (y + y')
  /-- (O4) Suprema of increasing sequences are additive. -/
  isLUB_add : ∀ {f g : ℕ → S}, Monotone f → Monotone g → ∀ {s t : S},
    IsLUB (Set.range f) s → IsLUB (Set.range g) t →
    IsLUB (Set.range fun n => f n + g n) (s + t)

namespace IsCuSemigroup

variable {S : Type*} [PartialOrder S] [AddCommMonoid S]

/-- In a Cu-semigroup, `0` is compact. -/
theorem isCompactElem_zero (hS : IsCuSemigroup S) : IsCompactElem (0 : S) :=
  fun f _ _ _ _ => ⟨0, hS.zero_le (f 0)⟩

end IsCuSemigroup

end CuTensor
end GroupApproximation
