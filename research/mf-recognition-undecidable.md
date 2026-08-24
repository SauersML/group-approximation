---
rg: 2
id: mf-recognition-undecidable
kind: claim
title: MF is not recognizable from a finite presentation, and its failure is not even r.e.
distinct_from:
  operator-mf-is-a-markov-property: that is the premise of the argument and is established; this is the conclusion, which needs the construction as well.
  adian-rabin-transform-for-mf: that is the computable transformation the proof consumes; this is what the transformation buys once it exists.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Computability/BooneWordProblemUndecidable.lean
  - GroupApproximation/Computability/WordProblemRE.lean
  - GroupApproximation/Computability/MarkovMFConsequences.lean
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
  - GroupApproximation/Computability/MFRecognitionImpossible.lean
  - GroupApproximation/Endpoint/MFRecognitionAudit.lean
---

ESTABLISHED (2026-08-17), via `mf-recognition-undecidable-via-adian-rabin` once
all four of its prerequisites closed.  Manuscript `cor:undecidable`, in
`\subsection{Undecidability of MF recognition}` of `sec:consequences`:

> There is no algorithm that decides, from a finite presentation, whether the
> presented group is MF.  By the effective form of the Adian--Rabin
> construction, the set of finite presentations of non-MF groups is not even
> recursively enumerable.

Two assertions, and the second is strictly stronger than the first.  The
recursively enumerable set in the argument is the **uniform word problem** `W`,
at the *source* of the reduction, not the set of MF presentations: `W` is r.e.
because a positive instance carries a finite certificate, and Post's theorem
against the undecidability of `W` gives `Wᶜ ∉ RE`.  The Adian--Rabin
transformation `Δ` is computable with `MF(Δ x) ↔ W x`, so `Wᶜ ≤₀ NONMF`, and an
enumeration of `NONMF` would pull back along `Δ` to one of `Wᶜ`.  Nothing here
establishes that `MF` itself is r.e., and the second assertion does not need
it.  The manuscript's `cor:undecidable` states this correctly ("$W$ is
recursively enumerable, whereas its complement and the set of presentation
codes of non-MF groups are not"); the sentence that stood here did not, and is
replaced.

## Status: both assertions, unconditionally

The two closed forms are

    Computability.operatorMF_recognition_not_computable
      : not ComputablePred (MarkovMFConsequences.operatorMFProperty
                              PresentationCodes.semantics)
    WordProblemRE.operatorMF_negative_side_not_re
      : not REPred (fun code => not MarkovMFConsequences.operatorMFProperty
                                      PresentationCodes.semantics code)

both with axiom closure `[propext, Classical.choice, Quot.sound]`, both cited
by `cor:undecidable` in the manuscript with `\leanverified`, and neither taking
a hypothesis.  `notes/NON_MF_UNCONDITIONAL_BASELINE.txt` is empty, so the
unconditionality gate agrees.

Restated at `IsOperatorMF (PresentationCodes.Carrier c)`, and joined by the two
"no program" forms and the reduction that names the hardness, in
`GroupApproximation/Computability/MFRecognitionImpossible.lean`:

    MFRecognitionImpossible.mf_recognition_not_computable
      : not ComputablePred (fun c => IsOperatorMF (Carrier c))
    MFRecognitionImpossible.no_mf_decider
      : not exists f, Computable f and (forall c, f c = true <-> IsOperatorMF (Carrier c))
    MFRecognitionImpossible.nonMF_presentations_not_re          -- NONMF not in RE
      : not REPred (fun c => not IsOperatorMF (Carrier c))
    MFRecognitionImpossible.no_nonMF_enumerator
      : no computable f : N -> Option PresentationCode prints only non-MF codes
        and eventually prints every one
    MFRecognitionImpossible.no_nonMF_certificate_system
      : no type of certificates with a computable checker is sound and complete
        for non-MF-ness -- NONMF has no recursively checkable proof system
    MFRecognitionImpossible.exists_manyOne_reduction_wordProblem_to_operatorMF
      : W <=0 MF and W-complement <=0 NONMF by one computable transformation,
        i.e. NONMF is coRE-hard
    MFRecognitionImpossible.exists_halting_reduction_to_operatorMF
      : a fixed modular machine with undecidable configuration-halting, and a
        computable compiler p |-> presentation that is MF iff p halts, so
        Halt <=0 MF and Halt-complement <=0 NONMF.  This fixes no level of the
        arithmetical hierarchy for MF; it is the hardness direction only
    MFRecognitionImpossible.mf_recognition_impossible
      : all of the above as one proposition, plus both sides inhabited

Every one of these is audited with `#audit_closed_axioms` in
`GroupApproximation/Endpoint/MFRecognitionAudit.lean`, which rejects a leading
declaration input as well as an axiom outside the classical three --- the check
that distinguishes a proved Adian--Rabin transform from an accepted one.

## How it was conditional, and what removed each condition

The node below is kept as it was written, because the decomposition it argues
for is what made the closure cheap.  What was complete and unconditional
already:

- the Markov-property premise, in full, including the isomorphism-invariance
  clause the prose leaves implicit: [[operator-mf-is-a-markov-property]];
- the recursion-theoretic inference the manuscript performs *after* the
  construction is available:
  `AdianRabinMarkovProperty.negativeSide_not_re_of_re_of_not_computablePred`
  — if a predicate is r.e. and not computable, its complement is not r.e.
  This is the step that turns "undecidable" into "not even r.e.", and it is a
  general fact with no group theory in it;
- the conditional consequences themselves,
  `MarkovMFConsequences.operatorMF_recognition_undecidable` and
  `operatorMF_negative_side_not_re`, which are closed theorems taking an
  `AdianRabinReduction` as an argument.

What was missing was that argument: [[adian-rabin-transform-for-mf]].  No
Adian--Rabin theorem was ever asserted as an axiom in `GroupApproximation/`,
and no reduction datum ever stood in for one — which is why the closure is a
construction and not a retraction.  It arrived in three pieces:

- the reduction datum itself, `AdianRabinVariantTransform.reduction`, all four
  fields, correctness first and `Computable transform` second;
- the undecidable source *in coordinates*,
  [[uniform-word-problem-on-presentation-codes-undecidable]], which the
  reduction structure does not supply and which
  [[novikov-boone-fp-group-undecidable-word-problem]] does not give in usable
  form;
- enumerability of the positive side *of the word problem*,
  [[word-problem-of-finite-presentation-is-re]], which is what Post's theorem
  needs against the previous item to reach the second assertion.  The route
  into this claim argued for that input in prose while omitting it from its
  `requires`; it is listed now.

## Why the conditional form was the right shape to keep

Splitting the corollary into "premises + inference" (proved) and "the
construction" (open) was not a bookkeeping convenience: it made the trust
surface a single named object rather than a sentence in prose, and it kept the
consequence usable.  That is exactly how it paid off — whoever supplied the
transform got both assertions with no re-proof, because the interfaces already
fit.  The estimate was right about the shape and wrong about the size in one
direction only: D6, quoted at 100--200 mechanical lines, was mechanical, but
the table had not seen that D4' and `Computable transform` were separate
coordinate obligations rather than corollaries of D4 and `correct`.
