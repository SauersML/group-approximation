---
rg: 2
id: uniform-word-problem-on-presentation-codes-undecidable
kind: claim
title: The word problem is undecidable as a predicate on presentation codes
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: that is the abstract existence statement, and it is established; this asks for the same group in coordinates, because `Group.IsFinitelyPresented` is a Prop-valued class and records no code, no generator numbering, and no words.
  word-problem-of-finite-presentation-is-re: that is D2, the positive instances of the word problem being recursively enumerable for an arbitrary code; this is the negative fact for one particular code, and neither implies the other.
  mf-recognition-undecidable: that is undecidability of recognising MF among finite presentations, the endpoint; this is undecidability of the *source* predicate the reduction to that endpoint starts from.
  markov-post-undecidable-monoid-word-problem: that is the monoid statement over a rewriting system, with no presentation coding in it; this is about `PresentationCodes.PresentationCode`, a Primcodable type of group presentations.
artifacts:
  - GroupApproximation/Computability/AdianRabinWordProblem.lean
  - GroupApproximation/Computability/PresentationCodes.lean
  - GroupApproximation/Computability/NovikovBoone.lean
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
  - GroupApproximation/Computability/BooneWords.lean
  - GroupApproximation/Computability/BooneWordMapPrimrec.lean
  - GroupApproximation/Computability/BooneWordAgreement.lean
  - GroupApproximation/Computability/UniformWordProblemUndecidable.lean
  - GroupApproximation/Computability/BooneWordProblemUndecidable.lean
---

ESTABLISHED (2026-08-17), via
[[uniform-word-problem-on-presentation-codes-undecidable-proof]]:
`Computability.not_computablePred_wordProblemPred` in
`Computability/BooneWordProblemUndecidable` says the word problem, taken as a
predicate on `PresentationCode × List (ℕ × Bool)` where
`PresentationCode = ℕ × List (List (ℕ × Bool))`, is not decidable.
Unconditional, with no literature input; the undecidable source at the bottom
is Mathlib's `ComputablePred.halting_problem`.  In the same module,
`Computability.operatorMF_recognition_not_computable` applies the reduction of
[[adian-rabin-transform-for-mf]] and discharges
[[mf-recognition-undecidable]]'s recognition half outright.

This is *not* [[novikov-boone-fp-group-undecidable-word-problem]], and the
difference is the reason this node exists rather than the graph treating the
obligation as discharged.

## Why the established theorem does not already give it

`NovikovBoone.exists_finitelyPresented_wordProblem_not_computablePred` produces
a group `G`, a proof of `Group.IsFinitelyPresented G`, and a sequence of
*elements* `g : ℕ → G` with `fun m => g m = 1` not computable.  To contradict
computability of `wordProblemPred` one needs a code `c₀` and a **computable**
`w : ℕ → List (ℕ × Bool)` with `wordOf c₀ (w m)` trivial exactly when
`g m = 1`.

Half of that is free.  In Mathlib

    class Group.IsFinitelyPresented (G) [Group G] : Prop where
      out : ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G),
              Function.Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated

so choice extracts `n`, `φ` and a finite normal generating set, and a code `c₀`
for `G` therefore exists; that it cannot be *computed* is irrelevant, since a
constant function at a noncomputable value is still computable.

The other half is not free.  The sequence is of elements, and preimages under a
chosen `φ` carry no computability guarantee whatever: nothing in the Prop says
that `m ↦ (some word representing g m)` is computable, and for a `φ` produced
by choice there is no reason it should be.  Undecidability of a sequence of
elements does not transport across a noncomputable presentation.

## Status, 2026-08-17 evening: all four pieces done, the join instantiated

* **The undecidable source, on configurations** --- done.
  `ModularMachineConfigHalting.exists_modularMachine_config_halting_not_computablePred`
  gives `∃ mm, ¬ComputablePred fun p : ℕ × ℕ => mm.Halts p`, axiom-clean.  This
  is the form with no indexing map, which is what lets words be attached to a
  configuration directly.  Reaching it needed the index map computable, and that
  needed **no** `Primrec` through `PartrecToTM2 → TM2to1 → TM1to0`: the map only
  builds an *initial* configuration, so it is a constant beside a Horner fold
  over the binary digits of the input, and the choice-based symbol encoding
  contributes fixed naturals rather than needing evaluation.
* **The code** --- done.  `BooneGroupCode.finalGroupCodeEquiv` :
  `Carrier (finalGroupCode mm hM) ≃* FinalGroup mm hM`.  The tower presentation
  had never said the group it presented *was* `FinalGroup`; the two agree only by
  transporting an equality of subgroups that occurs in the type of the HNN
  extension.
* **Coded triviality as a decidable search** --- done.
  `CodedWordTriviality.wordOf_eq_one_iff_exists_steps`, via normalisation past the
  dependent type and the deletion certificate of [[word-problem-of-finite-presentation-is-re]]'s
  raw-word route.
* **The words** --- done, in three layers plus the join.  `BooneWords` writes
  `k⁻¹ · t(α,β) · k · t(α,β)⁻¹` as raw data over four fixed generator indices
  and proves the presentation reads it as the halting element
  (`equiv_commElt`).  `BooneWordMapPrimrec.computable_rawComm` makes the
  configuration-to-word map computable --- the indices come off a choice-based
  enumeration and never need to evaluate, since a constant at a noncomputable
  value is still `Primrec`.  `BooneWordAgreement.wordProblem_rawComm_iff`
  moves the code's word problem on the raw word to `commElt P q = 1` by
  transporting *triviality* across the renumbering
  (`mk_relabel_eq_one_iff`), never tracking an element through the four
  equivalences of `stageCodeEquiv`.  `BooneWordProblemUndecidable` closes with
  Simpson's Theorem 8 stated at a **variable** associated subgroup, so
  `machineTowerPres_tsub` --- an equality of subgroups occurring in the *type*
  of the HNN extension --- can be `subst`ituted, and instantiates the join of
  `UniformWordProblemUndecidable`, which threads a single machine through both
  halves.

## What closed it

Not new mathematics — coordinates.  The Boone group's presentation is explicit:
base group `⟨t, x, y | xy = yx⟩`, one HNN stable letter per machine quadruple,
then `k`.  The words are explicit too, `t⁻¹ · finalTw (f m) · t ·
(finalTw (f m))⁻¹` with `f` computable.  What had never been written down was
either object *in a generator numbering*, because every step before this had a
reason not to need one: `HNNFinitePresentation` works through Mathlib's
quotient-of-coproduct definition and never builds a relator list, and the
word-problem half works in the tower's own generators.

So the obligation was to exhibit `c₀` together with the computable `w`, and to
prove the two agree --- which the modules above do.  Called **D4'** in the
cost table of [[adian-rabin-transform-for-mf]] and in
`Computability/AdianRabinMarkovProperty`; it carried no mathematical risk and
came in near its 200--400 line estimate.

## Why it is load-bearing

`MarkovMFConsequences.operatorMF_recognition_undecidable` takes
`¬ComputablePred sourceProperty` as a hypothesis alongside the reduction datum.
With `sourceProperty` concretized to `wordProblemPred` --- which it now is ---
that hypothesis is exactly this claim.  It is not supplied by the Markov
premise and it is not supplied by the transformation, so a route to
[[mf-recognition-undecidable]] that lists only those two is under-specified:
it would read as solved with the endpoint still unproved.  The same gap sits
behind the "D6 is 100--200 mechanical lines" estimate, which assumed this step
came free from D4.

With the claim established that hypothesis is discharged, and the positive
clause of `cor:undecidable` --- no algorithm decides MF from a presentation
code --- is unconditional.  The negative-side clause followed the same day:
its remaining hypothesis was the r.e. half, and
[[word-problem-of-finite-presentation-is-re]] supplies it
(`WordProblemRE.rePred_wordProblemPred`), so
`WordProblemRE.operatorMF_negative_side_not_re` carries no hypothesis either
and [[mf-recognition-undecidable]] is closed in both of its assertions.
