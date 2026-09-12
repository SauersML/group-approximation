---
rg: 2
id: ring-rank-approximability-forces-non-linear-soficity
kind: route
title: The ring-approximability equivalence has a false ring side, so it already makes the Leavitt unit group non-linear-sofic
target: non-linear-sofic-group
requires:
  - leavitt-unit-linear-soficity-is-ring-rank-approximability
  - toeplitz-isometry-defects-have-total-rank-at-least-one
artifacts:
  - research/artifacts/leavitt-ring-rank-approximability-collapse-2026-09-12.md
---

Let `K` be a finite field of characteristic `p` and `R = L_K(1,2)`.

- **The ring side is false.** By `toeplitz-isometry-defects-have-total-rank-at-least-one` (artifact
  Corollary 4), no unital `F_p`-linear `phi : R -> M_n(F_p)` is `1/3`-multiplicative on the pairs
  `(t_0,s_0)`, `(t_1,s_1)` and `(t_1,s_0)`. So the right-hand side of
  `leavitt-unit-linear-soficity-is-ring-rank-approximability` fails.
- **Then the group side is false.** The equivalence makes its left-hand side false: `R^x` is not
  `F_p`-linear sofic. That is `non-linear-sofic-group` with `F = F_p`.

**What this route records.** The Plan 2 claim is not an intermediate step toward the gate: it already
carries the payoff. `ring-rank-approximability-from-leavitt-el3-triviality` is its partner route, and
the two together place the claim between the gate instance and the payoff.
