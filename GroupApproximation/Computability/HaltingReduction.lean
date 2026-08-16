import GroupApproximation.Computability.PresentationCodes
import Mathlib.Computability.Halting

/-!
# The undecidable source is a theorem, not a hypothesis

`Computability.MarkovMFConsequences` derives undecidability of MF recognition
from two things: an Adian--Rabin reduction, and an *undecidable source problem*
for it to reduce from.  The source was left as a hypothesis, and the manuscript
supplied it by citing Novikov--Boone: a finitely presented group with unsolvable
word problem.

That citation is unnecessary.  The reduction interface does not care that the
source is a word problem --- it asks only for a computable map of codes and a
correctness equivalence --- so the source can be the halting problem, which
Mathlib already proves undecidable:

* `ComputablePred.halting_problem` --- the halting set is not computable;
* `ComputablePred.halting_problem_not_re` --- its complement is not even
  recursively enumerable.

Instantiating there discharges *both* undecidability hypotheses outright.  What
had been "assume a finitely presented group with unsolvable word problem, and
assume an Adian--Rabin construction for it" becomes "assume a computable map
from halting instances to presentations that tracks MF-ness".  One assumption
instead of two, and the one that remains is a single computable function rather
than a classical theorem.

This does not make the corollary unconditional: constructing that map is
Novikov--Boone and Adian--Rabin together, and neither is formalized here.  It
does mean the manuscript no longer needs to cite the undecidability of anything.
-/

namespace GroupApproximation
namespace MarkovMFConsequences

universe v

/-- The halting problem at a fixed input, as a predicate on partial recursive
codes. -/
def haltingProperty (n : ℕ) : Nat.Partrec.Code → Prop :=
  fun c ↦ (Nat.Partrec.Code.eval c n).Dom

/-- The halting problem is undecidable.  This is Mathlib's theorem, restated
against the predicate the reduction interface consumes. -/
theorem not_computablePred_haltingProperty (n : ℕ) :
    ¬ ComputablePred (haltingProperty n) :=
  ComputablePred.halting_problem n

/-- The complement of the halting problem is not recursively enumerable. -/
theorem not_rePred_haltingProperty_compl (n : ℕ) :
    ¬ REPred (fun c ↦ ¬ haltingProperty n c) :=
  ComputablePred.halting_problem_not_re n

/-- **MF recognition is undecidable, given a reduction alone.**  No
undecidability is assumed: the source problem is the halting problem, and its
undecidability is Mathlib's theorem. -/
theorem operatorMF_recognition_undecidable_of_haltingReduction :
    ∀ {Code : Type v} [Primcodable Code]
      (semantics : FinitePresentationSemantics Code) (n : ℕ)
      (_reduction : AdianRabinReduction (haltingProperty n)
        (operatorMFProperty semantics)),
      ¬ ComputablePred (operatorMFProperty semantics) := by
  intro Code _ semantics n reduction
  exact recognition_undecidable reduction (not_computablePred_haltingProperty n)

/-- **The negative side is not recursively enumerable, given a reduction
alone.**  Again nothing about the source is assumed. -/
theorem operatorMF_negative_side_not_re_of_haltingReduction :
    ∀ {Code : Type v} [Primcodable Code]
      (semantics : FinitePresentationSemantics Code) (n : ℕ)
      (_reduction : AdianRabinReduction (haltingProperty n)
        (operatorMFProperty semantics)),
      ¬ REPred (fun code ↦ ¬ operatorMFProperty semantics code) := by
  intro Code _ semantics n reduction
  exact negative_side_not_re reduction (not_rePred_haltingProperty_compl n)


/-! ## Pinning the coding

`FinitePresentationSemantics` does **not** require the code-to-group map to be
effective.  That is a real loophole: one could define, noncomputably,
`Carrier c := if (eval c 0).Dom then PUnit else MarkedGroup`, and then
`operatorMFProperty` would literally *be* the halting predicate, giving an
unconditional undecidability theorem with no reduction at all.  It would say
nothing about groups --- the code-to-group map is not computable, so deciding
the property from a code is not deciding anything from a presentation.

The statements below close that off by pinning the coding to
`PresentationCodes.semantics`, where the group really is read syntactically off
the code.  For that coding the hypothesis cannot be met vacuously: the only way
to supply the reduction is to build presentations from machines. -/

/-- **MF recognition for the actual presentation coding is undecidable, given a
reduction.**  The coding is fixed to the recursive one, so no noneffective
choice of semantics can make this true cheaply. -/
theorem presentationCodes_recognition_undecidable_of_haltingReduction :
    ∀ (n : ℕ)
      (_reduction : AdianRabinReduction (haltingProperty n)
        (operatorMFProperty PresentationCodes.semantics)),
      ¬ ComputablePred (operatorMFProperty PresentationCodes.semantics) := by
  intro n reduction
  exact recognition_undecidable reduction (not_computablePred_haltingProperty n)

/-- The non-r.e. statement, likewise pinned to the actual coding. -/
theorem presentationCodes_negative_side_not_re_of_haltingReduction :
    ∀ (n : ℕ)
      (_reduction : AdianRabinReduction (haltingProperty n)
        (operatorMFProperty PresentationCodes.semantics)),
      ¬ REPred (fun code ↦
        ¬ operatorMFProperty PresentationCodes.semantics code) := by
  intro n reduction
  exact negative_side_not_re reduction (not_rePred_haltingProperty_compl n)

end MarkovMFConsequences
end GroupApproximation
