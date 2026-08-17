---
rg: 2
id: machine-halting-is-one-word-equation-proof
kind: route
title: Simulate the machine by a semi-Thue system, then clean up to one fixed word
target: machine-halting-is-one-word-equation
requires: []
artifacts:
  - GroupApproximation/Computability/PostMachineHalting.lean
  - GroupApproximation/Computability/RewriteSimulation.lean
  - GroupApproximation/Computability/RewriteConfluence.lean
  - GroupApproximation/Computability/RewriteDeterminism.lean
  - GroupApproximation/Computability/RewriteInvariants.lean
  - GroupApproximation/Computability/TM0WordProblem.lean
---

## Direct proof, machine-checked

The forward direction is a simulation and the backward direction is the work.

**Forward.**  Each machine transition becomes a rewriting rule on the word
encoding a configuration (`RewriteSimulation`), so a halting run gives a
derivation from the initial word to a halted configuration word, and the
cleanup rules of `haltingSystem` then erase the tape and collapse the halted
word to the fixed `finalWord`.  Derivations compose in context
(`Derives.context`, `Derives.append`), which is all this direction needs.

**Backward.**  An arbitrary derivation between the two words has to be shown
to force a halting run, and the equation is in the *monoid* -- Thue
equivalence, not one-directional rewriting.  The machinery for that is
`RewriteInvariants` (quantities preserved by every rule), `RewriteDeterminism`
(from a configuration word at most one rule applies, so a derivation out of it
is forced) and `RewriteConfluence`.  Together they make the equivalence class
of a configuration word a single computation, so equality with `finalWord` can
only be reached by running the machine to a halt.

**Assembly.**  `PostMachineTM0.eval_dom_iff` identifies the hand-written
machine of `Computability.PostMachine` with Mathlib's `TM0.eval`, and
`TM0WordProblem` composes.  `FiniteMachineWordProblem` then adds the state
restriction: `MachineRestrict.restrict` cuts the machine down to a `Finset`
of states closed under transitions and proves the run is unchanged, which is
what makes the alphabet -- and hence the rule list -- finite.
