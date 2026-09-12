---
rg: 2
id: commutant-density-trace-blind-proof
kind: route
title: Character formula for the commutant dimension, and its two degeneracies
target: commutant-density-trace-blind
requires: []
artifacts:
  - notes/TRUE_WALL_ENERGY_AND_COMMUTANT_DENSITY.md
---

Complete written argument in the artifact.  Three steps.

1. `Ad rho` is a unitary representation on `(M_d,||.||_2)` with fixed space
   `rho(Gamma)'`; the Kazhdan sequence converges in norm to the projection
   onto that fixed space uniformly over representations, and
   `Tr(Ad rho(gamma))=|Tr rho(gamma)|^2`.  Divide by `d^2`.
2. `|tr(A)-tr(B)|<=||A-B||_2` and `| |a|^2-|b|^2 |<=2|a-b|` turn the
   multiplicative defect on the finite window into a bound on the difference
   of the two densities; a trace is conjugation invariant, so the limits
   coincide.
3. `mu_j(1)=<lambda(mu_j)delta_1,delta_1>->0` because an infinite group has
   no invariant vector in its regular representation.
