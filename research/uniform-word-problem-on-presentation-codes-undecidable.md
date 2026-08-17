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
---

OPEN.  `¬ ComputablePred AdianRabinWordProblem.wordProblemPred`: the word
problem, taken as a predicate on `PresentationCode × List (ℕ × Bool)` where
`PresentationCode = ℕ × List (List (ℕ × Bool))`, is not decidable.

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

## What closes it

Not new mathematics — coordinates.  The Boone group's presentation is explicit:
base group `⟨t, x, y | xy = yx⟩`, one HNN stable letter per machine quadruple,
then `k`.  The words are explicit too, `t⁻¹ · finalTw (f m) · t ·
(finalTw (f m))⁻¹` with `f` computable.  What has never been written down is
either object *in a generator numbering*, because every step so far had a
reason not to need one: `HNNFinitePresentation` works through Mathlib's
quotient-of-coproduct definition and never builds a relator list, and the
word-problem half works in the tower's own generators.

So the obligation is to exhibit `c₀` together with the computable `w`, and to
prove the two agree.  Called **D4'** in the cost table of
[[adian-rabin-transform-for-mf]] and in
`Computability/AdianRabinMarkovProperty`; on the order of 200--400 lines, with
no mathematical risk and a dependence on D1 (the coding layer).

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

None of this touches the manuscript's conditionality, which rests on D5.
