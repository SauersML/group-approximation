import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.ChosenNonMFTheorem
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Free-product consequences of an operator-MF obstruction

The canonical factor maps into a group free product are injective.  Since
operator-MF passes to subgroups, a non-MF factor forces the whole free product
to be non-MF.  This is the group-theoretic core of the companion note's
`E * Z` and `W * Z` deductions; no unavailable `C*`-simplicity API is hidden in
the statement.
-/

namespace GroupApproximation

universe u v

open scoped Monoid.Coprod

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- An operator-MF free product has an operator-MF left factor. -/
theorem IsOperatorMF.of_coprod_left (h : IsOperatorMF (G ∗ H)) :
    IsOperatorMF G :=
  h.comap Monoid.Coprod.inl Monoid.Coprod.inl_injective

/-- An operator-MF free product has an operator-MF right factor. -/
theorem IsOperatorMF.of_coprod_right (h : IsOperatorMF (G ∗ H)) :
    IsOperatorMF H :=
  h.comap Monoid.Coprod.inr Monoid.Coprod.inr_injective

/-- A non-operator-MF left factor obstructs the entire free product. -/
theorem not_isOperatorMF_coprod_left (hG : ¬ IsOperatorMF G) :
    ¬ IsOperatorMF (G ∗ H) :=
  fun h ↦ hG h.of_coprod_left

/-- A non-operator-MF right factor obstructs the entire free product. -/
theorem not_isOperatorMF_coprod_right (hH : ¬ IsOperatorMF H) :
    ¬ IsOperatorMF (G ∗ H) :=
  fun h ↦ hH h.of_coprod_right

/-- Free products preserve finite presentability.  This named wrapper makes
the exact library fact consumed by the companion note visible at the public
API boundary. -/
theorem coprod_isFinitelyPresented [Group.IsFinitelyPresented G]
    [Group.IsFinitelyPresented H] : Group.IsFinitelyPresented (G ∗ H) :=
  inferInstance

namespace ChosenFreeProductConsequences

open ChosenMarkedPresentation ChosenNonMFTheorem

/-- Unconditional finitely presented non-MF free product with an infinite
cyclic factor, using the fully kernel-checked chosen Shalom-cover witness. -/
theorem chosen_coprod_int_finitelyPresented_not_isOperatorMF :
    Group.IsFinitelyPresented (MarkedGroup ∗ Multiplicative ℤ) ∧
      ¬ IsOperatorMF (MarkedGroup ∗ Multiplicative ℤ) :=
  ⟨inferInstance,
    not_isOperatorMF_coprod_left
      chosenFinitelyPresented_not_isOperatorMF.2⟩

end ChosenFreeProductConsequences

end GroupApproximation
