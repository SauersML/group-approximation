---
rg: 2
id: mf-recognition-undecidable-via-adian-rabin
kind: route
title: Feed the Markov premise and the transformation into the reduction
target: mf-recognition-undecidable
requires: [operator-mf-is-a-markov-property, adian-rabin-transform-for-mf, uniform-word-problem-on-presentation-codes-undecidable, word-problem-of-finite-presentation-is-re]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Computability/MarkovMFConsequences.lean
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
  - GroupApproximation/Computability/BooneWordProblemUndecidable.lean
  - GroupApproximation/Computability/WordProblemRE.lean
---

## Why sufficient

The first two prerequisites are exactly the four fields of
`MarkovMFConsequences.AdianRabinReduction`: the first supplies the
`Primcodable` code type, the `FinitePresentationSemantics`, and the
`MarkovWitness`; the second supplies the computable `transform` and its
`correct` equivalence.  Given the structure, both halves of the target are
*already closed theorems* in the repository — this route is complete the
instant its prerequisites are, and as of 2026-08-17 they are.

The **fourth** prerequisite was missing from this route until 2026-08-17, for
the same reason as the third and with the same consequence.  The target has two
assertions, and the second one — "not even recursively enumerable" — is Post's
theorem, which needs the positive side r.e. *as well as* undecidable.  The
paragraph below said so in prose ("r.e. because the word problem of a finite
presentation is r.e. (D2 in the prerequisite's cost table)") while the
`requires` list did not, so the route promised the second assertion on the
strength of three inputs that cannot deliver it.  D2 is
[[word-problem-of-finite-presentation-is-re]]; it is now listed, and it is now
established.

The third prerequisite was missing from this route until 2026-08-16, and its
absence was not cosmetic either.  `operatorMF_recognition_undecidable` takes
`¬ComputablePred sourceProperty` as a hypothesis *alongside* the reduction
datum; the argument below contradicts "undecidability of the source", and
nothing in the structure supplies it.  With `sourceProperty` concretized to
`AdianRabinWordProblem.wordProblemPred`, that hypothesis is
[[uniform-word-problem-on-presentation-codes-undecidable]] — which is **not**
[[novikov-boone-fp-group-undecidable-word-problem]], because the latter is
stated for an abstract group and a sequence of elements, and
`Group.IsFinitelyPresented` is a Prop carrying no code and no words.  Listing
only the first two would have let this route read as solved with the endpoint
still unproved.

**Undecidability.**  `MarkovMFConsequences.recognition_undecidable`, then
`operatorMF_recognition_undecidable`.  Suppose MF-recognition on codes were
computable.  Composing with the computable `transform` makes the source word
problem computable (`computablePred_comp`), contradicting undecidability of
the source.  The `correct` field is what makes the composite the source
predicate: `w = 1` gives a trivial, hence MF, presentation, and `w != 1` gives
one containing `E`, hence non-MF by the forbidden-subgroup clause.

**Not even recursively enumerable.**  `negative_side_not_re`, then
`operatorMF_negative_side_not_re`, resting on the general
`negativeSide_not_re_of_re_of_not_computablePred`: a predicate that is r.e. and
not computable has a non-r.e. complement.  Applied to the set of MF
presentations — r.e. because the word problem of a finite presentation is r.e.
(D2 in the prerequisite's cost table), not computable by the first half — the
complement, the non-MF presentations, is not r.e.  `rePred_comp` transports
enumerability across the computable transform.

## Four prerequisites, and why none is the target restated

The Markov premise is a statement about groups and codes with no algorithm in
it; the transform is an algorithm with no MF in it; the third and fourth are
statements about a word problem on codes, with no MF in either.  None mentions
decidability of MF-recognition, and each can hold without the others.  What
makes the conjunction sufficient is the reduction argument above, which is real
content and is where `correct` is consumed.

Concretely, the four are discharged by
`PresentationCodes.markovWitness` (with the semantics and the code type),
`AdianRabinVariantTransform.reduction`,
`Computability.not_computablePred_wordProblemPred` and
`WordProblemRE.rePred_wordProblemPred`; the two halves of the conclusion they
compose into are `Computability.operatorMF_recognition_not_computable` and
`WordProblemRE.operatorMF_negative_side_not_re`.
