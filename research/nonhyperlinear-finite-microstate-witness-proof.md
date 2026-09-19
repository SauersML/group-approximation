---
rg: 2
id: nonhyperlinear-finite-microstate-witness-proof
kind: route
title: Diagonalize increasingly accurate canonical microstates
target: nonhyperlinear-group-has-finite-canonical-microstate-witness
requires:
  - finite-matrix-defect-zero-is-exact-ultraproduct-realizability
---

Negating the finite obstruction gives `1/n`-microstates on an exhaustion of
the countable group.  Their matrix ultraproduct has exact multiplication and
the canonical character, hence is injective.  Tensoring every coordinate by
an identity matrix preserves all normalized trace and HS quantities exactly.

In the `kappa_Gamma` formulation, restriction of canonical microstates gives
`kappa_Gamma(E)=0` for every finite `E`.  Conversely, choose a `1/n` tuple
for the `n`th window from `kappa_Gamma(E_n)=0`; the same diagonal sequence is
a canonical hyperlinear microstate system.  Negating this equivalence gives
one finite `E` with one strictly positive, all-dimensions gap.
