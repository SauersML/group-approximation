---
rg: 2
id: kazhdan-pauli-one-word-localization-proof
kind: route
title: Average the Gram over the actor and then over one Weyl orbit
target: kazhdan-transitive-pauli-actor-localizes-one-mixed-word
requires: []
artifacts:
  - research/artifacts/dual-prefix-kazhdan-reynolds-localization-2026-08-21.md
---

Actor spectral gap places `T` within
`epsilon_K/sqrt(kappa)` of its actor average `Tbar`.  Transitivity makes all
nonzero Weyl commutators of `Tbar` conjugate to the one prototype
commutator.  Averaging their squared norms and using the exact Pauli Reynolds
identity gives `(KPR9)`.  This is the desired unweighted square function;
no union bound over the `2^N` Weyl coordinates occurs.
