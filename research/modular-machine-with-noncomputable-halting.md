---
rg: 2
id: modular-machine-with-noncomputable-halting
kind: claim
title: Some modular machine has non-computable halting set
distinct_from:
  undecidable-post-turing-machine: That is established, and is about a Turing machine in Mathlib's TM0 form; this asks for a MODULAR machine in the sense of Aanderaa-Cohen, and the simulation connecting the two is exactly what is missing.
  markov-post-undecidable-monoid-word-problem: That is the monoid word problem and is established; this is a statement about machines with no words in it, and neither implies the other.
artifacts:
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
---

OPEN, and item **S9** of the roadmap in `Computability/BooneGroupBase`.
Simpson's Theorem 4: there is a modular machine `M` whose halting set
`H_M subseteq N x N` is not computable.

## Deliberately absent from Lean

This statement is **not stated in the development anywhere** -- not as a
hypothesis, not as a named predicate, not as a structure field.  That is a
design decision, recorded in `Computability/BooneGroupModularMachine`: nothing
below S9 depends on it, because stages S3--S7 produce the halting
biconditional for an *arbitrary* modular machine, and the undecidability
capstone is a two-line corollary to be written only once this is proved.  Not
naming it is what makes it impossible for a repository theorem to depend on it
silently.

## What proving it would take

A simulation of a Turing machine by a modular machine: encode the tape as the
base-`M` digits of the two coordinates, one quadruple per transition.  The
undecidable source is already in hand -- [[undecidable-post-turing-machine]] is
established with no literature input -- so what is missing is the simulation
itself and the transport of non-computability across it, not an undecidable
problem to start from.

Note the direction of the reduction: the halting *set* has to be
non-computable as a subset of `N x N`, uniformly in the configuration, which is
what the group construction reads.  A machine undecidable only on a sparse
family of inputs would not do, so `Mathlib/Computability/Reduce.lean` is the
tool for the last step.
