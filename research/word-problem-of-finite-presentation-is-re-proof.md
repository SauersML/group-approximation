---
rg: 2
id: word-problem-of-finite-presentation-is-re-proof
kind: route
title: One unbounded search over raw certificates, made Primcodable
target: word-problem-of-finite-presentation-is-re
requires: []
artifacts:
  - GroupApproximation/Computability/WordProblemRE.lean
  - GroupApproximation/Computability/AdianRabinWordProblem.lean
  - GroupApproximation/Computability/PresentationCodes.lean
---

Direct establishment.  `WordProblemRE.rePred_wordProblemPred` reads

```text
REPred AdianRabinWordProblem.wordProblemPred
```

and `wordProblemPred` is `fun x : PresentationCode x List (N x Bool) =>
WordProblem x.1 x.2` (`AdianRabinWordProblem`), which is the displayed
statement of the target verbatim.  `requires: []` is a proof commitment: the
argument is complete in the cited modules, with no hypothesis and no
literature input.

## How the dependent type was got past

The obstruction the claim recorded was real — `rawValue c cert` lands in
`FreeGroup (Fin (genCount c))`, a type depending on the code, and an unbounded
search ranges only over `Primcodable` data.  The module removes it by never
forming that element:

* `certWord` turns a raw certificate into a plain word by list surgery, and
  `wordOf_certWord` says the code reads it as the product of conjugates;
* `wordOf_testWord_eq_one_iff` restates the certificate matrix of
  `wordProblemPred_iff` as one equation between raw words, so
  `searchCheck : (PresentationCode x List (N x Bool)) -> RawCertificate -> Bool`
  is a decidable test on `Primcodable` data, and
  `wordProblemPred_iff_exists` is the resulting existential;
* `primrec_certWord`, `primrec_searchCheck` and `computable_searchCheck` are
  the `Primrec` plumbing the claim called the tedious half;
* `rePred_exists_eq_true` finishes with `Partrec.dom_re` against an unbounded
  `Nat.rfind`, which is the bridge the claim named — and not `Computable.find`,
  which the claim correctly warned demands a total search.

Soundness stays unconditional by design: a relator the code does not list
decodes to `1`, so the search can only ever certify genuine positive
instances.

## What it discharges

D2 of the cost table in `adian-rabin-transform-for-mf`.  Together with
`uniform-word-problem-on-presentation-codes-undecidable` it gives Post's
theorem both of its inputs, which is how `WordProblemRE.operatorMF_negative_side_not_re`
becomes unconditional and the second clause of the manuscript's
`cor:undecidable` stops being conditional.

Axiom closure, checked against the built environment on 2026-08-17:
`[propext, Classical.choice, Quot.sound]`.
