---
rg: 2
id: positive-rokhlin-everywhere-gives-maximal-bernoulli-entropy
kind: route
title: Positive Rokhlin entropy for every group gives every group an infinite supremum and maximal Bernoulli entropy
target: bernoulli-rokhlin-entropy-maximal-for-every-group
requires:
  - every-group-has-positive-rokhlin-entropy-action
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

By Seward's Theorem 1.11 in the second prerequisite, POS for every countably
infinite group gives INF for every countably infinite group. For a finite
alphabet `A`, Theorem 1.10 then gives
`h^Rok_G(A^G) = min{log|A|, infinity} = log|A|`.

This route and `maximal-bernoulli-entropy-everywhere-gives-positive-rokhlin`
record an equivalence of the two universal statements. The dependency cycle they
form is intended.
