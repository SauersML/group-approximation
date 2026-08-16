import GroupApproximation.Computability.PresentationCodeCompleteness
import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine.PostTuringMachine

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
to supply the reduction is to build presentations from machines.

## Asking for exactly the printed hypothesis

They also ask for no more than the manuscript grants.  What the corollary
supposes is a *single* object --- a computable map from halting instances to
presentation codes, correct in the sense that the coded group is MF exactly
when the instance halts --- whereas `AdianRabinReduction` bundles that map with
a `MarkovWitness`.  At this coding the witness is not a further assumption but a
closed theorem, `PresentationCodes.markovWitness`, so the statements below take
the printed data alone and assemble the reduction internally.

The recognition predicate is also spelled out rather than left as
`operatorMFProperty`: the hypothesis and the conclusion both speak of
`IsOperatorMF (PresentationCodes.Carrier _)`, the group the code presents, which
is the same predicate by `PresentationCodes.operatorMFProperty_semantics` and
leaves nothing for an ineffective reading of "semantics" to hide behind.

## DO NOT factor the reduction assembly into a `def`

Each proof below writes the `AdianRabinReduction` out inline.  That is not a
style choice, and undoing it silently breaks a repository-wide gate.

`scripts/check_non_mf_unconditional.py` decides which premises are undischarged
by a least fixed point over *producers*: a declaration whose conclusion head is
`AdianRabinReduction`, and whose own premises are not themselves corpus types,
marks `AdianRabinReduction` as something the corpus produces.  A named

    noncomputable def haltingReductionOfTransform … : AdianRabinReduction …

qualifies --- its premises are a plain function, a `Computable`, and an `Iff`,
none of them corpus types --- so adding it retires the `conditional-data`
finding on *every* declaration in the development that takes a reduction as a
premise, `operatorMF_recognition_undecidable` included.  The gate goes green and
the conditionality stops being tracked, which is precisely backwards: nothing
here produces a reduction, these theorems consume a hypothesised transform, and
the corollary is conditional on exactly that.

This was written that way once and caught before landing.  Keep it inline. -/

/-- **MF recognition for the actual presentation coding is undecidable.**  The
hypothesis is the printed one and nothing besides: a computable map sending each
halting instance to a presentation code whose group is MF exactly when that
instance halts.  The coding is fixed to the recursive one, so no noneffective
choice of semantics can make this true cheaply, and the Markov witness the
reduction interface also wants is supplied by a theorem rather than assumed. -/
theorem presentationCodes_recognition_undecidable_of_haltingReduction :
    ∀ (n : ℕ)
      (transform : Nat.Partrec.Code → PresentationCodes.PresentationCode)
      (_transform_computable : Computable transform)
      (_correct : ∀ c, IsOperatorMF (PresentationCodes.Carrier (transform c)) ↔
        haltingProperty n c),
      ¬ ComputablePred (fun code : PresentationCodes.PresentationCode ↦
        IsOperatorMF (PresentationCodes.Carrier code)) := by
  intro n transform htransform hcorrect hdecidable
  have reduction : AdianRabinReduction (haltingProperty n)
      (operatorMFProperty PresentationCodes.semantics) :=
    { markov := PresentationCodes.markovWitness
      transform := transform
      transform_computable := htransform
      correct := fun c ↦
        (PresentationCodes.operatorMFProperty_semantics (transform c)).trans
          (hcorrect c) }
  exact recognition_undecidable reduction
    (not_computablePred_haltingProperty n)
    (hdecidable.of_eq fun code ↦
      (PresentationCodes.operatorMFProperty_semantics code).symm)

/-- The non-r.e. statement, on the same printed hypothesis and likewise pinned to
the actual coding: the set of presentation codes of non-MF groups is not
recursively enumerable. -/
theorem presentationCodes_negative_side_not_re_of_haltingReduction :
    ∀ (n : ℕ)
      (transform : Nat.Partrec.Code → PresentationCodes.PresentationCode)
      (_transform_computable : Computable transform)
      (_correct : ∀ c, IsOperatorMF (PresentationCodes.Carrier (transform c)) ↔
        haltingProperty n c),
      ¬ REPred (fun code : PresentationCodes.PresentationCode ↦
        ¬ IsOperatorMF (PresentationCodes.Carrier code)) := by
  intro n transform htransform hcorrect hre
  have reduction : AdianRabinReduction (haltingProperty n)
      (operatorMFProperty PresentationCodes.semantics) :=
    { markov := PresentationCodes.markovWitness
      transform := transform
      transform_computable := htransform
      correct := fun c ↦
        (PresentationCodes.operatorMFProperty_semantics (transform c)).trans
          (hcorrect c) }
  exact negative_side_not_re reduction
    (not_rePred_haltingProperty_compl n)
    (hre.of_eq fun code ↦
      not_congr (PresentationCodes.operatorMFProperty_semantics code).symm)

/-! ## The same socket, against Mathlib's Post--Turing machine

`Computability.TM0WordProblem` ends at

    (TM0.eval M l).Dom ↔ mk R (encode (liftCfg (ofInput l))) = mk R finalWord

so `(Turing.TM0.eval M l).Dom` is the predicate the machine half of the
development speaks in.  The two theorems below are the wrappers above with the
source problem in that shape, so a reduction built on that side plugs in without
a translation step: same conclusion, same internally supplied Markov witness,
and a `transform` out of `List Γ` rather than out of `Nat.Partrec.Code`.

They are *not* what the manuscript's corollary is badged against, and the
difference is not stylistic.  The printed text says the corollary "reduces from
the halting problem, whose undecidability and whose non-enumerable complement
are proved in the accompanying formalization".  For `Nat.Partrec.Code` that is
true --- `ComputablePred.halting_problem` and `halting_problem_not_re` are
Mathlib theorems, discharged above with no hypothesis.  For `Turing.TM0.eval`
nothing in Mathlib or in this repository yet proves it; obtaining it is the
`ToPartrec.exists_code`/`PartrecToTM2.tr_eval`/`TM2to1.tr_eval`/`TM1to0.tr_eval`
chain, which is not attempted anywhere here.  So undecidability appears below as
an explicit hypothesis, and stating the badged endpoints this way would have
added to `cor:undecidable` an assumption the printed sentence denies it makes.

Only Mathlib's `TM0` is imported, never the machine modules themselves: the
statements have to compose with that lane, not depend on it while it is still
being built. -/

/-- **MF recognition is undecidable, from an undecidable Post--Turing machine.**
The reduction is the printed one --- a computable map from inputs to presentation
codes whose group is MF exactly when the machine terminates --- and the Markov
witness is again supplied internally.  What is *not* supplied is undecidability
of `Turing.TM0.eval M`, which is a hypothesis here because nothing yet proves
it; the halting-problem form above needs no such hypothesis. -/
theorem presentationCodes_recognition_undecidable_of_tm0Reduction :
    ∀ {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ]
      (M : Turing.TM0.Machine Γ Λ)
      (_machine_undecidable :
        ¬ ComputablePred (fun l : List Γ ↦ (Turing.TM0.eval M l).Dom))
      (transform : List Γ → PresentationCodes.PresentationCode)
      (_transform_computable : Computable transform)
      (_correct : ∀ l, IsOperatorMF (PresentationCodes.Carrier (transform l)) ↔
        (Turing.TM0.eval M l).Dom),
      ¬ ComputablePred (fun code : PresentationCodes.PresentationCode ↦
        IsOperatorMF (PresentationCodes.Carrier code)) := by
  intro Γ Λ _ _ _ M hmachine transform htransform hcorrect hdecidable
  have reduction : AdianRabinReduction
      (fun l : List Γ ↦ (Turing.TM0.eval M l).Dom)
      (operatorMFProperty PresentationCodes.semantics) :=
    { markov := PresentationCodes.markovWitness
      transform := transform
      transform_computable := htransform
      correct := fun l ↦
        (PresentationCodes.operatorMFProperty_semantics (transform l)).trans
          (hcorrect l) }
  exact recognition_undecidable reduction hmachine
    (hdecidable.of_eq fun code ↦
      (PresentationCodes.operatorMFProperty_semantics code).symm)

/-- The non-r.e. side of the same socket.  As above, non-enumerability of the
machine's divergent inputs is a hypothesis rather than a theorem. -/
theorem presentationCodes_negative_side_not_re_of_tm0Reduction :
    ∀ {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [Primcodable Γ]
      (M : Turing.TM0.Machine Γ Λ)
      (_machine_negative_not_re :
        ¬ REPred (fun l : List Γ ↦ ¬ (Turing.TM0.eval M l).Dom))
      (transform : List Γ → PresentationCodes.PresentationCode)
      (_transform_computable : Computable transform)
      (_correct : ∀ l, IsOperatorMF (PresentationCodes.Carrier (transform l)) ↔
        (Turing.TM0.eval M l).Dom),
      ¬ REPred (fun code : PresentationCodes.PresentationCode ↦
        ¬ IsOperatorMF (PresentationCodes.Carrier code)) := by
  intro Γ Λ _ _ _ M hmachine transform htransform hcorrect hre
  have reduction : AdianRabinReduction
      (fun l : List Γ ↦ (Turing.TM0.eval M l).Dom)
      (operatorMFProperty PresentationCodes.semantics) :=
    { markov := PresentationCodes.markovWitness
      transform := transform
      transform_computable := htransform
      correct := fun l ↦
        (PresentationCodes.operatorMFProperty_semantics (transform l)).trans
          (hcorrect l) }
  exact negative_side_not_re reduction hmachine
    (hre.of_eq fun code ↦
      not_congr (PresentationCodes.operatorMFProperty_semantics code).symm)

end MarkovMFConsequences
end GroupApproximation
