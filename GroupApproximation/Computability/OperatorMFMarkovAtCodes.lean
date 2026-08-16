import GroupApproximation.Computability.PresentationCodeCompleteness

/-!
# Operator-MF is a Markov property, at the level of codes

An Adian--Rabin construction consumes three things about the property it is
going to make undecidable, and produces a computable transformation from
them:

1. the property is an isomorphism invariant of the presented group;
2. some finitely presented group has it;
3. some finitely presented group embeds in **no** group with it.

`Computability.OperatorMFMarkovWitness` established (2) and (3) at the level
of *groups*.  `Computability.PresentationCodeCompleteness` transported the
witnesses to *codes*.  This file adds (1) and packages all three, so the
entire Markov-property input to Adian--Rabin is discharged at the coding where
the reduction has to live.

What remains of `MarkovMFConsequences.AdianRabinReduction` after this file is
one field and one field only: the computable `transform` together with its
correctness equivalence.  Producing it is the Adian--Rabin construction, whose
own input is a finitely presented group with undecidable word problem
(Novikov--Boone).  That is the sole remaining literature input of the
development, and nothing else about it is outstanding.
-/

namespace GroupApproximation
namespace PresentationCodes

open MarkovMFConsequences

/-- Operator-MF is an isomorphism invariant: transport a faithful corona
representation along the isomorphism. -/
theorem isOperatorMF_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : IsOperatorMF G) : IsOperatorMF H :=
  IsOperatorMF.comap h e.symm.toMonoidHom e.symm.injective

/-- **(1) Isomorphism invariance at the coding.**  Two codes presenting
isomorphic groups have the same recognition status, so the predicate really is
a property of the presented group rather than of the presentation. -/
theorem operatorMFProperty_congr {c c' : PresentationCode}
    (h : Nonempty (Carrier c ≃* Carrier c')) :
    operatorMFProperty semantics c ↔ operatorMFProperty semantics c' := by
  obtain ⟨e⟩ := h
  rw [operatorMFProperty_semantics, operatorMFProperty_semantics]
  exact ⟨fun hc ↦ isOperatorMF_congr e hc, fun hc ↦ isOperatorMF_congr e.symm hc⟩

/-- **(3) at the coding, in forbidden-subgroup form.**  The negative code
presents a group that injects into no operator-MF group at all, which is
strictly stronger than merely failing the property. -/
theorem negativeCode_forbidden_subgroup :
    ∀ (H : Type) [Group H], IsOperatorMF H →
      ∀ f : Carrier negativeCode →* H, ¬ Function.Injective f := by
  intro H _ hH f hf
  obtain ⟨en⟩ :=
    (exists_code_mulEquiv ChosenMarkedPresentation.MarkedGroup).choose_spec
  refine OperatorMFMarkovWitness.chosen_forbidden_subgroup hH
    (f.comp en.symm.toMonoidHom) ?_
  exact hf.comp en.symm.injective

/-- **The complete Markov-property input to Adian--Rabin, at the coding.**
Isomorphism invariance, a positive code, a negative code, and the
forbidden-subgroup strength of the negative code.  Everything an Adian--Rabin
construction needs about operator-MF is here; what it still needs about
*groups* is a finitely presented one with undecidable word problem. -/
theorem operatorMF_isMarkovAtCodes :
    (∀ c c' : PresentationCode, Nonempty (Carrier c ≃* Carrier c') →
        (operatorMFProperty semantics c ↔ operatorMFProperty semantics c')) ∧
      operatorMFProperty semantics positiveCode ∧
      ¬ operatorMFProperty semantics negativeCode ∧
      (∀ (H : Type) [Group H], IsOperatorMF H →
        ∀ f : Carrier negativeCode →* H, ¬ Function.Injective f) :=
  ⟨fun _ _ h ↦ operatorMFProperty_congr h,
    isOperatorMF_positiveCode,
    not_isOperatorMF_negativeCode,
    negativeCode_forbidden_subgroup⟩

end PresentationCodes
end GroupApproximation
