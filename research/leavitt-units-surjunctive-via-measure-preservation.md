---
rg: 2
id: leavitt-units-surjunctive-via-measure-preservation
kind: route
title: Measure preservation plus full support gives surjunctivity of the Leavitt unit group
target: leavitt-unit-group-surjunctive
requires:
  - injective-measure-preserving-ca-is-surjective
  - injective-cas-over-leavitt-units-preserve-uniform-bernoulli
artifacts:
  - research/artifacts/gottschalk-kazhdan-direct-attack-2026-09-12.md
---

If every injective cellular automaton over `U = L_{F_2}(1,2)^x` preserves the
uniform Bernoulli measure (`injective-cas-over-leavitt-units-preserve-uniform-bernoulli`),
then by `injective-measure-preserving-ca-is-surjective` every such automaton is
surjective, so `U` is surjunctive.

This is an elementary, measure-theoretic route distinct from the Rokhlin-entropy
route `positive-rokhlin-entropy-makes-leavitt-units-surjunctive`: it needs only
preservation of the uniform measure, not a positive-entropy free action. The open
prerequisite is where property (T) and spectral gap must do their work; the
full-support step is free.
