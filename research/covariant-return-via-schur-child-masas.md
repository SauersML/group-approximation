---
rg: 2
id: covariant-return-via-schur-child-masas
kind: route
title: Pay the predicate Reynolds core by returning the two transverse Schur children
target: compressor-covariant-packet-reynolds-return
requires:
  - schur-packet-child-square-is-pauli-transverse
  - compressor-returns-schur-child-masas
  - scaled-kazhdan-transport
  - bounded-overlap-syndrome-energy-accounting
---

The Schur child-square theorem replaces the additive controlled coefficients
by two genuine finite subgroup commutants.  On each forbidden simple block,
their centered modules are orthogonal and have dimension `m^2`; their sum is
part of the three-coefficient Reynolds core.  The compressor-return claim
identifies those two modules on the same fixed-scale carrier with transport
cost paid by named relators.  Equation `(SPS4)` converts the attempted common
return into a lower bound for that relator energy, and bounded overlap sums
the local charges.  Allowed sectors admit a common refinement and contribute
no forced charge.  This yields `(CPR1)` on the positive forbidden core needed
by the parent route.

