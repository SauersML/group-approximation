import GroupApproximation.Computability.AdianRabinGeneral

/-!
# Operator-MF as Markov data, and the general machine reproducing the special case

`Computability.AdianRabinVariantTransform` runs the Adian--Rabin construction
for operator-MF directly.  `Computability.AdianRabinGeneral` abstracts that
construction over an arbitrary Markov property.  This file closes the loop:
operator-MF *is* such a property, so the general theorem reproduces the
concrete undecidability result, and the abstraction is therefore faithful
rather than a weakening.

The three clauses are all already proved in the repository:

* heredity is `IsOperatorMF.comap`;
* free groups are residually finite, hence operator-MF, which is exactly the
  step `RabinVariantMF.pres_isOperatorMF` takes;
* `PresentationCodes.isOperatorMF_positiveCode` and
  `not_isOperatorMF_negativeCode` are the two codes.

`recognition_undecidable_general` is the concrete conclusion of
`AdianRabinVariantTransform`, obtained instead from the general theorem.

## Manuscript status

Certifies that `Computability.AdianRabinGeneral` subsumes the operator-MF
construction it was abstracted from.
-/

namespace GroupApproximation
namespace OperatorMFMarkovData

open PresentationCodes AdianRabinGeneral

/-- Free groups are operator-MF: they are countable and residually finite. -/
theorem isOperatorMF_freeGroup (α : Type) [Countable α] :
    IsOperatorMF (FreeGroup α) :=
  isOperatorMF_of_residuallyFinite

/-- **Operator-MF is a Markov property.** -/
noncomputable def operatorMFMarkovData :
    MarkovData (fun (H : Type) (_ : Group H) ↦ IsOperatorMF H) where
  hereditary f hf hK := hK.comap f hf
  free α _ := isOperatorMF_freeGroup α
  positiveCode := positiveCode
  positive := isOperatorMF_positiveCode
  forbidden := negativeCode
  forbidden_not := not_isOperatorMF_negativeCode

/-- **The general theorem reproduces the concrete one.**  Operator-MF
recognition is undecidable, obtained from `AdianRabinGeneral` rather than from
the hand-run construction of `AdianRabinVariantTransform`. -/
theorem recognition_undecidable_general
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred
      (codeProperty (fun (H : Type) (_ : Group H) ↦ IsOperatorMF H)) :=
  recognition_undecidable_of_wordProblem operatorMFMarkovData h

/-- The negative side is not recursively enumerable either. -/
theorem negative_side_not_re_general
    (h : ¬ REPred (fun x ↦ ¬ AdianRabinWordProblem.wordProblemPred x)) :
    ¬ REPred (fun c ↦ ¬ IsOperatorMF (Carrier c)) :=
  negative_side_not_re_of_wordProblem operatorMFMarkovData h

/-- The property the general machine computes with is the printed one. -/
theorem codeProperty_eq_operatorMFProperty (c : PresentationCode) :
    codeProperty (fun (H : Type) (_ : Group H) ↦ IsOperatorMF H) c
      ↔ MarkovMFConsequences.operatorMFProperty semantics c :=
  Iff.rfl

end OperatorMFMarkovData
end GroupApproximation
