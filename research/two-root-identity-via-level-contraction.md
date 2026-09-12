---
rg: 2
id: two-root-identity-via-level-contraction
kind: route
title: A level-independent deviation that tends to zero along levels is zero
target: rank-models-of-el3-satisfy-the-two-root-identities
requires:
  - corner-rank-data-cannot-contract-the-two-root-deviation
  - leavitt-corner-deviations-are-level-independent
  - leavitt-corner-deviations-vanish-along-levels
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

## Why sufficient

Let `sigma` be a characteristic-two rank model of `EL_3(R)`, `R = L_(F_2)(1,2)`.

* Part 3 of `corner-rank-data-cannot-contract-the-two-root-deviation` makes the branch deviation
  `delta(k)` a function of the level alone.
* `leavitt-corner-deviations-are-level-independent` gives `delta(k) = delta(0)` for all `k`.
* `leavitt-corner-deviations-vanish-along-levels` gives `delta(k) -> 0`.

So `delta(0) = 0`. By part 2 of `el3-two-root-violation-splits-over-leavitt-branches`,
`delta(0) = rk(n_23(e_0) n_12(e_0))` is the deviation of the branch model `sigma o iota_0`, whose
vanishing makes that model trivial by `two-root-identity-is-corner-local-for-leavitt-rank-models`;
the same node then makes `sigma` trivial, so in particular `N_23 N_12 = 0`. In characteristic two
`N_12^2 = 0` holds automatically, so both two-root identities hold and the target is met.

## Status

Both prerequisites are OPEN, so this route establishes nothing yet. It is recorded because it
isolates the two halves that remain after
`corner-rank-data-cannot-contract-the-two-root-deviation` removes every contraction available from
corner data: additivity of branch ranks is refuted, and the root displacements are exactly constant
across levels.

*Verification by `w3-vf-linear` (2026-09-12), Section 16.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: valid and conditional; both prerequisites are OPEN. Notation: rk(n_23(e_0)n_12(e_0)) is delta(1). delta(0) is the unit pair itself, so delta(0) = 0 is N_23N_12 = 0 directly.*
