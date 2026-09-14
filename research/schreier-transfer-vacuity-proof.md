---
rg: 2
id: schreier-transfer-vacuity-proof
kind: route
title: A Kazhdan simple host has no proper co-amenable subgroup, and an invariant mean on an orbit integrates to an invariant measure
target: schreier-transfer-vacuous-on-kazhdan-and-boundary-hosts
requires:
  - simple-kazhdan-groups-have-no-proper-co-amenable-subgroups
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

Section 4 of the artifact.

- **Kazhdan hosts.** With `D` generating `G`, the Schreier graph is connected, and Følner sets make `H`
  co-amenable. So `H = G`, and `Fix_G` is the constant configurations. An injective automaton permutes
  these finitely many points.
- **Measure-free actions.**
  - An invariant mean `m` on `G/G_y` defines `Lambda(f) = m(g G_y |-> f(g y))`, a positive, unital,
    invariant functional on `C(Y)`. Riesz turns it into an invariant probability measure.
  - For `V`, invariance under `0 -> 00, 10 -> 01, 11 -> 1` gives `mu[0] = mu[00]`. The transposition
    `00 <-> 01` gives `mu[00] = mu[01]`, so `mu[0] = 2 mu[0] = 0`. The swap `0 <-> 1` gives
    `mu[1] = mu[0] = 0`.
