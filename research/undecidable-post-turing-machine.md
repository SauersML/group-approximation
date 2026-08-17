---
rg: 2
id: undecidable-post-turing-machine
kind: claim
title: A Post-Turing machine whose halting on a computable family of inputs is undecidable
artifacts:
  - GroupApproximation/Computability/UniversalMachineUndecidable.lean
  - GroupApproximation/Computability/UniversalCode.lean
  - GroupApproximation/Computability/UniversalCodeHalting.lean
  - GroupApproximation/Computability/UniversalMachineInit.lean
---

ESTABLISHED, unconditionally and with no literature input.
`Computability.UniversalMachineUndecidable.tm0_halting_not_computablePred`:
for every `n` there is a single `Turing.TM0` machine `M` and a family of
inputs `l : N -> List G` with

    not ComputablePred (fun m => (TM0.eval M (l m)).Dom).

The machine is Mathlib's translation of a `ToPartrec.Code`, obtained by
`ToPartrec.exists_code` from a partial recursive function whose halting is
undecidable; the undecidable source is Mathlib's own
`ComputablePred.halting_problem`, so nothing here is quoted from the
literature.

## What the bridge in this file is for

`UniversalCodeHalting` produces a `Nat.Partrec.Code` with undecidable
halting; `ToPartrec.exists_code` consumes a *different* code type, in vector
form.  `Nat.Partrec'.part_iff1` is the conversion, and supplying it is the
only content of the file: everything on either side of it is Mathlib.

## Why it is stated for a machine rather than for a code

The consumer is [[machine-halting-is-one-word-equation]], which encodes
*configurations* of a machine as words.  A code has no configurations.  So
the undecidability has to be moved onto a machine before it can be moved onto
a word problem, and this is where that happens.

Note that the machine's state type `PartrecToTM2.L'` is infinite -- its
states carry continuations, which carry codes.  Cutting it down to a finite
set of states is a separate step and does not belong here; see
[[markov-post-undecidable-monoid-word-problem]] for where the finiteness
comes from and why it was already in Mathlib.
