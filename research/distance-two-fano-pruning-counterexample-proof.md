---
rg: 2
id: distance-two-fano-pruning-counterexample-proof
kind: route
title: Repeat one clause and mix all seven globally consistent assignments
target: distance-two-oracularity-does-not-force-fano-pruning
requires:
  - fano-cap-witness-sections-force-source-affine-safety
  - rstar-fano-ghost-affine-hull-criterion
---

The seven satisfying assignments of `(DTO1)` define seven scalar classical
strategies.  Their uniform direct sum is a finite-dimensional commutative
perfect strategy whose spectral support at every labeled clause is all seven
assignments.  Because the same sampled assignment is used in every copy,
all overlaps are exact and every neighborhood link contains its constant
tuple.  Global commutativity is stronger than distance-two commutativity.

After translating the forbidden assignment to zero, the support is
`F_2^3\{0}`, so it contains all seven Fano lines.  The affine-safety theorem
then gives the pp-reduction obstruction stated in `(DTO2)`, completing both
parts of the counterexample.

