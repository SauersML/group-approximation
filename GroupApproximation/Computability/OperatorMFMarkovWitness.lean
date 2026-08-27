import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# An unconditional Markov witness for operator-MF

This is the exact group-theoretic input used by the Adian--Rabin argument.
The syntactic Adian--Rabin transformation is not part of Mathlib, but the
positive witness and the finitely presented forbidden-subgroup witness are
fully kernel-checked here.
-/

namespace GroupApproximation
namespace OperatorMFMarkovWitness

open ChosenMarkedPresentation ChosenNonMFTheorem

universe u

/-- The trivial group is a finitely presented positive operator-MF witness. -/
theorem positive_punit :
    Group.IsFinitelyPresented PUnit.{1} ∧ IsOperatorMF PUnit.{1} :=
  ⟨inferInstance, isOperatorMF_of_finite_standard PUnit.{1}⟩

/-- The chosen finitely presented non-MF group cannot inject into any
operator-MF group.  This is stronger than merely being a negative example. -/
theorem chosen_forbidden_subgroup
    {H : Type u} [Group H] (hH : IsOperatorMF H)
    (f : MarkedGroup →* H) : ¬ Function.Injective f := by
  intro hf
  exact chosenFinitelyPresented_not_isOperatorMF.2 (hH.comap f hf)

/-- Existence form of the complete group-theoretic Markov witness: a
finitely presented negative group excluded from every operator-MF ambient
group. -/
theorem exists_finitelyPresented_forbidden_subgroup :
    ∃ (E : Type) (_ : Group E),
      Group.IsFinitelyPresented E ∧ ¬ IsOperatorMF E ∧
        ∀ (H : Type) [Group H], IsOperatorMF H →
          ∀ f : E →* H, ¬ Function.Injective f :=
  ⟨MarkedGroup, inferInstance,
    chosenFinitelyPresented_not_isOperatorMF.1,
    chosenFinitelyPresented_not_isOperatorMF.2,
    fun _ _ hH f ↦ chosen_forbidden_subgroup hH f⟩

end OperatorMFMarkovWitness
end GroupApproximation
