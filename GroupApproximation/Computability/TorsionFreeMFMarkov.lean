import GroupApproximation.Computability.TorsionFreeMarkov
import GroupApproximation.Computability.OperatorMFMarkovData

/-!
# "Torsion-free and operator-MF" is undecidable

The manuscript's Question 2 asks for a **torsion-free finitely presented
non-MF** group.  Whatever the answer, the *recognition* problem for the
positive side of that question --- being torsion-free and operator-MF --- is
undecidable, and this file proves it from the two Markov data already
available and the conjunction lemma `MarkovData.and`.

The conjunction needs one new input only: a code satisfying both properties.
The trivial group serves, being subsingleton and therefore finite, hence
residually finite, hence operator-MF, and vacuously torsion-free.

The forbidden code is inherited from either conjunct; here it is the
manuscript's own non-MF group, which embeds in no operator-MF group and so
in no torsion-free operator-MF group either.

## Manuscript status

A consequence of `Computability.AdianRabinGeneral`; certifies no manuscript
step on its own.
-/

namespace GroupApproximation
namespace TorsionFreeMFMarkov

open PresentationCodes AdianRabinGeneral

/-- The trivial group is operator-MF. -/
theorem isOperatorMF_trivialCode : IsOperatorMF (Carrier trivialCode) := by
  haveI := subsingleton_carrier_trivialCode
  haveI : Finite (Carrier trivialCode) := Finite.of_subsingleton
  exact isOperatorMF_of_residuallyFinite

/-- **Being torsion-free and operator-MF is a Markov property.** -/
noncomputable def torsionFreeMFMarkovData :
    MarkovData (fun (H : Type) (_ : Group H) ↦
      IsPowerTorsionFree H ∧ IsOperatorMF H) :=
  MarkovData.and TorsionFreeMarkov.torsionFreeMarkovData
    OperatorMFMarkovData.operatorMFMarkovData trivialCode
    TorsionFreeMarkov.isPowerTorsionFree_trivialCode isOperatorMF_trivialCode

/-- **Recognising "torsion-free and operator-MF" from a finite presentation is
undecidable.** -/
theorem torsionFreeMF_recognition_undecidable
    (h : ¬ ComputablePred AdianRabinWordProblem.wordProblemPred) :
    ¬ ComputablePred (codeProperty (fun (H : Type) (_ : Group H) ↦
      IsPowerTorsionFree H ∧ IsOperatorMF H)) :=
  recognition_undecidable_of_wordProblem torsionFreeMFMarkovData h

/-- The complementary side --- the side on which Question 2 lives --- is not
even recursively enumerable. -/
theorem torsionFreeMF_negative_side_not_re
    (h : ¬ REPred (fun x ↦ ¬ AdianRabinWordProblem.wordProblemPred x)) :
    ¬ REPred (fun c ↦ ¬ (IsPowerTorsionFree (Carrier c) ∧
      IsOperatorMF (Carrier c))) :=
  negative_side_not_re_of_wordProblem torsionFreeMFMarkovData h

end TorsionFreeMFMarkov
end GroupApproximation
