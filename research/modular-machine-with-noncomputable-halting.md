---
rg: 2
id: modular-machine-with-noncomputable-halting
kind: claim
title: Some modular machine has non-computable halting set
distinct_from:
  undecidable-post-turing-machine: That is about a Turing machine in Mathlib's TM0 form; this is about a MODULAR machine in the sense of Aanderaa-Cohen, and the simulation connecting the two is the content of the route below.
  markov-post-undecidable-monoid-word-problem: That is the monoid word problem and is established; this is a statement about machines with no words in it, and neither implies the other.
artifacts:
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
  - GroupApproximation/Computability/ModularMachineUndecidable.lean
  - GroupApproximation/Computability/QuadMachine.lean
  - GroupApproximation/Computability/QuadMachineTM0.lean
---

ESTABLISHED (2026-08-16),
`Computability/ModularMachineUndecidable.exists_modularMachine_halting_not_computablePred`.
Item **S9** of the roadmap in `Computability/BooneGroupBase`, and Simpson's
Theorem 4: there is a modular machine `M` whose halting set
`H_M subseteq N x N` is not computable.

## It was deliberately absent from Lean until it was proved

The statement was **not stated in the development anywhere** -- not as a
hypothesis, not as a named predicate, not as a structure field -- which is what
made it impossible for a repository theorem to depend on it silently.  Nothing
below S9 depended on it, because stages S3--S7 produce the halting biconditional
for an *arbitrary* modular machine, and the capstone was a two-line corollary
waiting on exactly this.  It is now a theorem rather than a debt, so the
discipline paid for itself: no statement had to be weakened when it arrived.

## What proving it took

Exactly the simulation anticipated here: the tape encoded as the base-`M` digits
of the two coordinates, one quadruple per transition.  The undecidable source
was already in hand ([[undecidable-post-turing-machine]], no literature input),
so what remained was the simulation and the transport, and that is
`QuadMachine` (a modular machine read as a two-stack machine) plus
`QuadMachineTM0` (two stacks simulating a Post-Turing tape).

Note the direction of the reduction: the halting *set* has to be
non-computable as a subset of `N x N`, uniformly in the configuration, which is
what the group construction reads.  A machine undecidable only on a sparse
family of inputs would not do, so `Mathlib/Computability/Reduce.lean` is the
tool for the last step.
