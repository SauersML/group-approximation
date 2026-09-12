---
rg: 2
id: strict-automaton-bounds-rokhlin-supremum-proof
kind: route
title: Read the supremum off Seward's minimum formula at the first amplified alphabet where the code saves more than the markers cost
target: strict-automaton-bounds-rokhlin-supremum
requires:
  - strict-automaton-lowers-bernoulli-rokhlin-entropy
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

At `k = k_0` the first prerequisite gives

    h^Rok_G((A^(k_0))^G) <= k_0 log q - k_0 delta/D + log 3 < k_0 log q,

since `k_0 delta/D > log 3`. By the second prerequisite the left side equals
`min{k_0 log q, h^Rok_sup(G)}`. The minimum is below `k_0 log q`, so it is the
supremum, which is therefore below `k_0 log q`. Section 6 of the artifact.
