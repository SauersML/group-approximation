import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Protecting a marked pair in a group quotient

Hull's construction protects the pair `{1, s}` at each quotient stage.  For a
literal quotient by a normal subgroup `N`, that geometric conclusion has a
small exact algebraic certificate: `s` is not in `N`.  This module records both
directions, so a finite relator computation can discharge protected-set
injectivity without repackaging it as an assumption.
-/

namespace GroupApproximation
namespace QuotientProtectedPair

universe u

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

/-- Avoidance of the marked element by the quotient kernel proves injectivity
on the protected pair `{1, s}`. -/
theorem injOn_pair_of_not_mem {s : G} (hs : s ∉ N) :
    Set.InjOn (QuotientGroup.mk' N) ({1, s} : Set G) := by
  have hqs : QuotientGroup.mk' N s ≠ QuotientGroup.mk' N 1 := by
    intro h
    apply hs
    apply (QuotientGroup.eq_one_iff s).mp
    simpa using h
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exfalso
    exact hqs hxy.symm
  · exfalso
    exact hqs hxy
  · rfl

/-- Conversely, if the marked element is nonidentity, injectivity on
`{1, s}` forces it to avoid the quotient kernel. -/
theorem not_mem_of_injOn_pair {s : G} (hs : s ≠ 1)
    (hinj : Set.InjOn (QuotientGroup.mk' N) ({1, s} : Set G)) : s ∉ N := by
  intro hsN
  apply hs
  apply hinj (show s ∈ ({1, s} : Set G) by simp)
    (show (1 : G) ∈ ({1, s} : Set G) by simp)
  have hq : QuotientGroup.mk' N s = 1 :=
    (QuotientGroup.eq_one_iff s).mpr hsN
  simpa using hq

/-- For a nonidentity marked element, kernel avoidance and protected-pair
injectivity are equivalent. -/
theorem injOn_pair_iff_not_mem {s : G} (hs : s ≠ 1) :
    Set.InjOn (QuotientGroup.mk' N) ({1, s} : Set G) ↔ s ∉ N :=
  ⟨not_mem_of_injOn_pair N hs, injOn_pair_of_not_mem N⟩

end QuotientProtectedPair
end GroupApproximation
