---
rg: 2
id: adian-rabin-transform-for-mf-proof
kind: route
title: The variant construction as list surgery, and its four assembled fields
target: adian-rabin-transform-for-mf
requires: []
artifacts:
  - GroupApproximation/Computability/AdianRabinVariantTransform.lean
  - GroupApproximation/Computability/RawTransform.lean
  - GroupApproximation/Computability/RawTransformPrimrec.lean
  - GroupApproximation/Computability/RabinVariantCode.lean
  - GroupApproximation/Computability/CoprodCode.lean
  - GroupApproximation/Computability/MarkovReductionInterface.lean
  - GroupApproximation/Computability/MarkovMFConsequences.lean
---

Direct establishment.  `AdianRabinVariantTransform.reduction` is a term of

```text
MarkovMFConsequences.AdianRabinReduction
  AdianRabinWordProblem.wordProblemPred
  (MarkovMFConsequences.operatorMFProperty PresentationCodes.semantics)
```

and that structure has exactly four fields — `markov`, `transform`,
`transform_computable`, `correct`.  Inhabiting it is what the target asks for:
a computable map on finite presentations, trivial-hence-MF when the input word
dies and containing the forbidden non-MF group when it survives, together with
the correctness equivalence in that form.  `requires: []` is a proof
commitment, not a placeholder.

## The two halves, and which one was the late one

**Correctness** (`correct`) closed first.  `transform` free-products the input
code with the fixed non-MF code and runs the variant construction on the
normalized word; `RabinVariantCode.variantCode_isOperatorMF` gives the collapse
direction — the output presents a free group, residually finite hence
operator-MF — and `RabinVariantCode.isOperatorMF_of_variantCode` the embedding
direction, after which the free product's non-MF factor would inherit
operator-MF and contradict `not_isOperatorMF_negativeCode`.  The bridge between
the input code's word problem and the free product's is
`AdianRabinVariantTransform.coprod_mk_eq_one_iff`.

**Computability** (`transform_computable`) was the obligation the claim
recorded as remaining, and it is closed the way the claim said it would have to
be: not by proving the existing `noncomputable def` computable, but by giving a
second definition and proving the two agree.  `RawTransform.rawTransform`
performs the same construction by pure list surgery,
`RawTransform.relSet_rawTransform` says the two codes name the same relators —
so `RawTransform.rawCarrierEquiv` is an isomorphism of the presented groups and
`AdianRabinVariantTransform.correct_raw` transports correctness across it — and
`RawTransformPrimrec.computable_rawTransform` supplies the field, through a
`Primrec₂` chain that never encodes a `FreeGroup` over the dependent alphabet
`Fin (genCount c)`.

## What the cost table now reads

D1, D3, D4 were already closed.  This route closes **D5** (the effective
construction) and **D6** (assembly).  D2 and D4' are the sibling claims
`word-problem-of-finite-presentation-is-re` and
`uniform-word-problem-on-presentation-codes-undecidable`, both now established
in their own right; with all of them the manuscript's one declared classical
literature input — the Adian--Rabin construction — is no longer an input.

The decomposition route `adian-rabin-transform-via-boone-source-and-rabin-chain`
stays as it is.  It reduces this claim to D4 together with
`rabin-chain-effective-collapse-dichotomy`, a uniform statement with no
computability in it; that reduction is still a correct one, and the claim it
routes through is still worth having, so nothing about it is retracted by the
target being reached another way.

Axiom closure of `reduction`, `correct_raw` and `computable_rawTransform`,
checked against the built environment on 2026-08-17:
`[propext, Classical.choice, Quot.sound]`.
