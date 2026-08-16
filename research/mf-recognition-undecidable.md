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
  - GroupApproximation/Computability/MarkovMFConsequences.lean
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
---

OPEN.  Manuscript `cor:undecidable`, in `\subsection{Undecidability of MF
recognition}` of `sec:consequences`:

> There is no algorithm that decides, from a finite presentation, whether the
> presented group is MF.  By the effective form of the Adian--Rabin
> construction, the set of finite presentations of non-MF groups is not even
> recursively enumerable.

Two assertions, and the second is strictly stronger than the first: the
positive side (MF presentations) is recursively enumerable by way of the r.e.
word problem, and if the negative side were r.e. too, the property would be
decidable — which the first assertion forbids.

## Status, and where exactly it is conditional

**MISSING** under this project's standard, and conditional at exactly one
point.  What is complete and unconditional:

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

What is missing is that argument: [[adian-rabin-transform-for-mf]].  No
Adian--Rabin theorem is asserted as an axiom anywhere in
`GroupApproximation/`, and no reduction datum stands in for one.

## Why the conditional form is the right shape to keep

Splitting the corollary into "premises + inference" (proved) and "the
construction" (open) is not a bookkeeping convenience: it makes the trust
surface a single named object rather than a sentence in prose, and it keeps the
consequence usable.  Anyone who later supplies the transform gets both
assertions immediately, with no re-proof, because the interfaces already fit —
D6 in the cost table of the prerequisite is 100--200 mechanical lines.
