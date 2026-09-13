import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Basic

/-!
# Sequential way-below and compact elements

A Cuntz semigroup `Cu(A)` is an ordered monoid in which every increasing sequence has a
supremum.  Its way-below relation `x ≪ y` says that every increasing sequence whose supremum
dominates `y` has a term dominating `x`, and `x` is *compact* when `x ≪ x`.  An isomorphism of
Cuntz semigroups is in particular an order isomorphism, so the way-below relation, the compact
elements, and the comparability of elements are invariants of `Cu(A)` up to isomorphism.

This file sets up that order-theoretic layer over an arbitrary preorder and proves its invariance
under order isomorphisms.  Nothing here is operator-algebraic.

## Main results

* `WayBelow`, `IsCompactElem`: sequential way-below and compact elements;
* `orderIso_wayBelow_iff`, `orderIso_isCompactElem_iff`: invariance under order isomorphisms;
* `not_nonempty_orderIso_of_incomparable`: two incomparable elements rule out an order
  isomorphism with a totally preordered set;
* `not_nonempty_orderIso_of_incomparable_compact`: the same with compact elements, against a
  target whose compact elements are pairwise comparable.
-/

namespace GroupApproximation
namespace CuTensor

variable {α β : Type*} [Preorder α] [Preorder β]

/-- **Sequential way-below.** `WayBelow a b` holds when every increasing sequence whose least
upper bound dominates `b` has a term dominating `a`. -/
def WayBelow (a b : α) : Prop :=
  ∀ f : ℕ → α, Monotone f → ∀ s : α, IsLUB (Set.range f) s → b ≤ s → ∃ n, a ≤ f n

/-- An element is *compact* when it is way below itself. -/
def IsCompactElem (a : α) : Prop := WayBelow a a

/-- A constant sequence has its value as least upper bound. -/
theorem isLUB_range_const (b : α) : IsLUB (Set.range fun _ : ℕ => b) b := by
  refine ⟨?_, fun _ hu => hu ⟨0, rfl⟩⟩
  rintro _ ⟨n, rfl⟩
  exact le_rfl

/-- Way-below implies below. -/
theorem WayBelow.le {a b : α} (h : WayBelow a b) : a ≤ b := by
  obtain ⟨n, hn⟩ := h (fun _ => b) (fun _ _ _ => le_rfl) b (isLUB_range_const b) le_rfl
  exact hn

/-- Pulling a least upper bound of a sequence back along an order isomorphism. -/
theorem isLUB_range_symm (e : α ≃o β) {g : ℕ → β} {t : β} (ht : IsLUB (Set.range g) t) :
    IsLUB (Set.range fun n => e.symm (g n)) (e.symm t) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact e.symm.monotone (ht.1 ⟨n, rfl⟩)
  · intro u hu
    have hg : t ≤ e u := ht.2 (by
      rintro _ ⟨n, rfl⟩
      exact e.symm_apply_le.1 (hu ⟨n, rfl⟩))
    exact e.symm_apply_le.2 hg

/-- Order isomorphisms preserve the way-below relation. -/
theorem wayBelow_map_orderIso (e : α ≃o β) {a b : α} (h : WayBelow a b) :
    WayBelow (e a) (e b) := by
  intro g hg t ht hbt
  obtain ⟨n, hn⟩ := h (fun n => e.symm (g n)) (fun i j hij => e.symm.monotone (hg hij))
    (e.symm t) (isLUB_range_symm e ht) (e.le_symm_apply.2 hbt)
  exact ⟨n, e.le_symm_apply.1 hn⟩

/-- The way-below relation is invariant under order isomorphisms. -/
theorem orderIso_wayBelow_iff (e : α ≃o β) {a b : α} :
    WayBelow (e a) (e b) ↔ WayBelow a b := by
  refine ⟨fun h => ?_, wayBelow_map_orderIso e⟩
  simpa using wayBelow_map_orderIso e.symm h

/-- Compact elements are invariant under order isomorphisms. -/
theorem orderIso_isCompactElem_iff (e : α ≃o β) {a : α} :
    IsCompactElem (e a) ↔ IsCompactElem a :=
  orderIso_wayBelow_iff e

/-- A preorder order-isomorphic to a totally preordered set is total. -/
theorem total_of_orderIso (e : α ≃o β) (h : ∀ x y : β, x ≤ y ∨ y ≤ x) (a b : α) :
    a ≤ b ∨ b ≤ a := by
  rcases h (e a) (e b) with h' | h'
  · exact Or.inl (e.le_iff_le.1 h')
  · exact Or.inr (e.le_iff_le.1 h')

/-- **Obstruction.** Two incomparable elements rule out any order isomorphism with a totally
preordered set. -/
theorem not_nonempty_orderIso_of_incomparable (h : ∀ x y : β, x ≤ y ∨ y ≤ x) {a b : α}
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) : ¬ Nonempty (α ≃o β) := by
  rintro ⟨e⟩
  rcases total_of_orderIso e h a b with h' | h'
  · exact hab h'
  · exact hba h'

/-- **Obstruction, compact form.** Two incomparable compact elements rule out any order
isomorphism with a preordered set whose compact elements are pairwise comparable. -/
theorem not_nonempty_orderIso_of_incomparable_compact
    (h : ∀ x y : β, IsCompactElem x → IsCompactElem y → x ≤ y ∨ y ≤ x) {a b : α}
    (ha : IsCompactElem a) (hb : IsCompactElem b) (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    ¬ Nonempty (α ≃o β) := by
  rintro ⟨e⟩
  rcases h (e a) (e b) ((orderIso_isCompactElem_iff e).2 ha)
      ((orderIso_isCompactElem_iff e).2 hb) with h' | h'
  · exact hab (e.le_iff_le.1 h')
  · exact hba (e.le_iff_le.1 h')

end CuTensor
end GroupApproximation
