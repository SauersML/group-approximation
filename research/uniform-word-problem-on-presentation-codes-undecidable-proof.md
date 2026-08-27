---
rg: 2
id: uniform-word-problem-on-presentation-codes-undecidable-proof
kind: route
title: A machine, its group in a generator numbering, and a computable word map
target: uniform-word-problem-on-presentation-codes-undecidable
requires: []
artifacts:
  - GroupApproximation/Computability/BooneWordProblemUndecidable.lean
  - GroupApproximation/Computability/UniformWordProblemUndecidable.lean
  - GroupApproximation/Computability/BooneWords.lean
  - GroupApproximation/Computability/BooneWordMapPrimrec.lean
  - GroupApproximation/Computability/BooneWordAgreement.lean
  - GroupApproximation/Computability/AdianRabinWordProblem.lean
  - GroupApproximation/Computability/PresentationCodes.lean
---

Direct establishment.  `Computability.not_computablePred_wordProblemPred`
reads

```text
not ComputablePred AdianRabinWordProblem.wordProblemPred
```

on `PresentationCode x List (N x Bool)`, which is the target.  `requires: []`
is a proof commitment: unconditional, with no literature input, the
undecidable source at the bottom being Mathlib's
`ComputablePred.halting_problem`.

## Why it is not `novikov-boone-fp-group-undecidable-word-problem`

That theorem produces a group, a `Group.IsFinitelyPresented` proof, and a
sequence of *elements*.  `Group.IsFinitelyPresented` is `Prop`-valued and
records no code, no generator numbering and no words, so nothing in it makes
`m |-> (a word representing g m)` computable.  The gap is coordinates, and
this route closes it in four pieces joined by
`UniformWordProblemUndecidable`:

* the source on configurations —
  `ModularMachineConfigHalting.exists_modularMachine_config_halting_not_computablePred`,
  the indexing-free form, so words attach to a configuration directly;
* the code — `BooneGroupCode.finalGroupCodeEquiv`, transporting an equality of
  subgroups occurring in the *type* of the HNN extension;
* the words — `BooneWords.equiv_commElt` writes the halting element as raw
  data over four fixed generator indices, `BooneWordMapPrimrec.computable_rawComm`
  makes the configuration-to-word map computable, and
  `BooneWordAgreement.wordProblem_rawComm_iff` moves triviality across the
  renumbering rather than tracking an element through four equivalences;
* the join — `exists_boone_words` feeds
  `not_computablePred_wordProblemPred_of_boone_words`, threading one machine
  through both halves.

## What it discharges

D4' of the cost table in `adian-rabin-transform-for-mf`, and the
`not ComputablePred sourceProperty` hypothesis that
`MarkovMFConsequences.operatorMF_recognition_undecidable` takes alongside the
reduction datum — a hypothesis supplied neither by the Markov premise nor by
the transformation, which is why `mf-recognition-undecidable-via-adian-rabin`
lists this claim separately.

Axiom closure, checked against the built environment on 2026-08-17:
`[propext, Classical.choice, Quot.sound]`.
