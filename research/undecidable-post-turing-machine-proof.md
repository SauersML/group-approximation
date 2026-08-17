---
rg: 2
id: undecidable-post-turing-machine-proof
kind: route
title: Bridge Mathlib's halting problem across the two code types
target: undecidable-post-turing-machine
requires: []
artifacts:
  - GroupApproximation/Computability/UniversalMachineUndecidable.lean
  - GroupApproximation/Computability/UniversalCodeHalting.lean
  - GroupApproximation/Computability/UniversalMachineInit.lean
---

## Direct proof, machine-checked

Three steps, all in the repository.

1. `UniversalCodeHalting` fixes a `Nat.Partrec.Code` running the `m`-th
   partial recursive code on a fixed input, so deciding whether it halts
   would decide which codes halt -- Mathlib's
   `ComputablePred.halting_problem`.  This is the only place undecidability
   enters, and it enters from Mathlib rather than from a citation.

2. `exists_toPartrec_code_not_computablePred` converts that code into a
   `Turing.ToPartrec.Code` with the same halting behaviour.  The conversion
   is `Nat.Partrec'.part_iff1`: it turns the underlying partial recursive
   function into the vector form `ToPartrec.exists_code` consumes.

3. `UniversalMachineInit` runs the resulting code as a Post-Turing machine,
   through Mathlib's `PartrecToTM2.tr_eval`, `TM2to1.tr_eval` and
   `TM1to0.tr_eval`, and `tm0_halting_not_computablePred` composes the three.

No hypothesis is carried, and the statement quantifies over the input family
explicitly, so nothing is hidden in a choice of encoding.
