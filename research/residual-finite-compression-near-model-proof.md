---
rg: 2
id: residual-finite-compression-near-model-proof
kind: route
title: Assemble finite regular quotients and compute the charge-null compression fixed space
target: kun-thom-compression-survives-amenable-near-model
requires:
  - kun-thom-nonsofic-wreath
  - infranormal-nonnormal-has-infinite-compression-orbit
  - hyperlinear-near-representation-criterion
---

Use the residual finite quotient representation `(KNA7)` and the ultralimit
of uniform basis measures `(KNA8)`.  This is a faithful exact representation,
the charge is invariant, and residual separation makes its charge character
regular.

For each finite quotient, the compressed subgroup is included in the parent
subgroup and conjugate to it.  Finite cardinality turns the inclusion into
equality.  Hence the two fixed projections are identical in every block and
the compressor normalizes their direct sum.  The normalized trace of the
block Reynolds projection is `1/|q_n(Gamma)|`; these orders tend to infinity,
so its charge is zero.  Faithfulness retains strictness of the abstract
subgroup images in the full direct sum.

This verifies every displayed assertion without invoking a repair or
stability theorem.
