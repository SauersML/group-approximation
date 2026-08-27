import Mathlib.GroupTheory.PresentedGroup

/-!
# Evaluation in a presented group

This file records the generic compatibility between evaluation of a free word
at the canonical generators of a presented group and its quotient map.  It is
shared by the two concrete presentation modules.
-/

namespace GroupApproximation

/-- Homomorphisms out of a free group agree on all words once they agree on
the free generators. -/
theorem freeGroup_hom_eq_on_generators {X M : Type*} [Group M]
    {f g : FreeGroup X →* M}
    (h : ∀ i, f (FreeGroup.of i) = g (FreeGroup.of i)) :
    ∀ w, f w = g w := by
  intro w
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · rw [map_one, map_one]
  · exact h
  · intro i hi
    rw [map_inv, map_inv, hi]
  · intro a b ha hb
    rw [map_mul, map_mul, ha, hb]

/-- Evaluating a free word at the canonical generators of a presented group is
the canonical quotient map. -/
theorem freeGroup_lift_presentedGroup_generators
    {X : Type*} {R : Set (FreeGroup X)} (w : FreeGroup X) :
    FreeGroup.lift (fun i ↦ PresentedGroup.mk R (FreeGroup.of i)) w =
      PresentedGroup.mk R w := by
  apply freeGroup_hom_eq_on_generators
  intro i
  simp

end GroupApproximation
