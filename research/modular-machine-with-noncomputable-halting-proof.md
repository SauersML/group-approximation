---
rg: 2
id: modular-machine-with-noncomputable-halting-proof
kind: route
title: A modular machine is a two-stack machine, and two stacks simulate a Post-Turing tape
target: modular-machine-with-noncomputable-halting
requires: [undecidable-post-turing-machine]
artifacts:
  - GroupApproximation/Computability/ModularMachineUndecidable.lean
  - GroupApproximation/Computability/QuadMachine.lean
  - GroupApproximation/Computability/QuadMachineTM0.lean
---

## Why sufficient

The prerequisite supplies a `Turing.TM0` machine whose halting on a computable
family of inputs is undecidable.  What this route adds is the simulation
carrying that to a *modular* machine, which is the one thing Simpson leaves to
the reader.

**A modular machine is a two-stack machine.**  Read a configuration `(α, β)` in
base `m`.  A step pops the last digit of each of `α` and `β` and pushes two
digits onto one of them --- so `α` and `β` are two stacks and a step moves one
cell from one to the other.  A modular machine *is* a Turing machine whose tape
has been cut at the head.  `QuadMachine` formalizes that reading: machines on
two digit stacks, with `encCfg` reading a configuration as a pair of naturals
and `step_encCfg` saying one machine step is one modular-machine step.

The design point that is forced: a step pushes onto exactly one stack, so the
state cannot stay on the same side when the head turns around.  A configuration
carries a `side` bit, and a move toward the back flips it; the quadruple table
never sees `side`, because the digit tags already determine it.

**Two stacks simulate a Post-Turing tape.**  `QuadMachineTM0` runs the
simulation in the other direction, and `ModularMachineUndecidable` composes:
`exists_reaches_restrict` cuts the machine down to the states a run visits, and
`exists_modularMachine_halting_not_computablePred` transports non-computability
across the encoding, giving a modular machine whose halting set is not
computable.

## Why this was the last external input

It is Simpson's Theorem 4, and the chain was deliberately built so that nothing
below it mentioned undecidability: S3--S7 produce the halting biconditional for
an *arbitrary* modular machine. With this proved, the capstone is two lines, and
the repository's Novikov--Boone has no literature input at all --- the only
undecidable source anywhere in it is Mathlib's `ComputablePred.halting_problem`.
