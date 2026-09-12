---
rg: 2
id: leavitt-bernoulli-preservation-from-surjunctivity
kind: route
title: Surjunctivity of the Leavitt unit group makes its injective automata bijective and so measure-preserving
target: injective-cas-over-leavitt-units-preserve-uniform-bernoulli
requires:
  - leavitt-unit-group-surjunctive
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - research/artifacts/gk-vf-positive-verification-2026-09-12.md
---

If `U = L_(F_2)(1,2)^x` is surjunctive, then every injective cellular automaton over
`U` is bijective, and bijective automata preserve the uniform Bernoulli measure over
every group. So every injective automaton over `U` preserves `mu_A`.

This is the converse of `leavitt-units-surjunctive-via-measure-preservation`. The two
routes record that the Leavitt measure-preservation claim is equivalent to
`leavitt-unit-group-surjunctive`, not a weaker target. The dependency cycle is
intended, and neither claim can establish the other on its own. Section 1.4 of the
artifact has the re-derivation.
