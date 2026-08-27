---
rg: 2
id: full-group-subgroup-trace-generation-dichotomy
kind: claim
title: A full-group subgroup has either the wrong trace or too small an algebra
distinct_from:
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that rules out promotion from an arbitrary non-CE trace by its GNS kernel; this computes the exact obstruction for the canonical unitaries of a countable subgroup of a relation full group.
  free-label-orthogonalization-erases-payload-trace: that tensors arbitrary payload unitaries with free labels and shows the labels can be recovered; this dichotomy needs no auxiliary labels and separates fixed-point trace from algebra generation inside the relation factor.
---

Let `R` be an ergodic aperiodic pmp equivalence relation on a diffuse
probability space, and let `Lambda <= [R]` be countable.  Write `v_g in L(R)`
for the canonical full-group unitaries.  Then exactly the following obstruction
applies to the proposed canonical group-factor compiler.

* If the `Lambda`-action is not essentially free, the representation
  `g |-> v_g` does not preserve the canonical group trace, since
  `tau_R(v_g)=mu(Fix(g))`.
* If it is essentially free, the representation extends to a trace-preserving
  embedding `L(Lambda)->L(R)`, but its image intersects the Cartan
  `L^infinity(X)` only in the scalars.  In particular its image cannot be all
  of `L(R)`.

Thus taking a countable subgroup of the full group cannot turn the non-CE
relation factor into a canonical group factor: fixed points carry the desired
relation information precisely when they spoil the regular trace, while
removing them leaves a proper group subalgebra.

