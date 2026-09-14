---
rg: 2
id: invariant-output-symmetry-must-be-core-free-proof
kind: route
title: A normal subgroup inside the output symmetry makes the automaton invariant under left translation
target: invariant-output-symmetry-must-be-core-free
requires: []
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Proposition 4 of the artifact.

1. Let `N <= H` be normal and `n in N`.
2. For every `g`, `ng = g(g^-1 n g)` with `g^-1 n g in H`. So `tau(x)(ng) = tau(x)(g)`, i.e.
   `tau(n^-1 . x) = tau(x)`.
3. Injectivity gives `n^-1 . x = x` for all `x`, and the shift is free, so `n = 1`.
4. For the memory group, restrict `tau` to `Gamma`, where the invariance holds for `g in Gamma`.
