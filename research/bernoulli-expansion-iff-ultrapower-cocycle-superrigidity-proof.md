---
rg: 2
id: bernoulli-expansion-iff-ultrapower-cocycle-superrigidity-proof
kind: route
title: Compactness in the metric ultrapower plus Popa at each finite level
target: bernoulli-expansion-iff-ultrapower-cocycle-superrigidity
requires:
  - popa-bernoulli-cocycle-superrigidity
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

Section 17 of the artifact (Theorem U).
- **(1) => (2).**
  - A cocycle `z` on `P_𝒰(A)` is represented by cochains `c_n` with `|delta c_n| -> 0`.
  - Expansion gives exact `z_n` with `|c_n - z_n| -> 0`, so `z = [z_n]`.
  - Popa gives `z_n = delta f_n + chi_n`. `Hom(Gamma, A)` is finite, so `chi_n` is `𝒰`-constant, and
    `z = delta [f_n] + chi`.
- **(2) => (1).**
  - If no rate works, there are `eta > 0` and cochains `c_n` with `|delta c_n| -> 0` and distance at least `eta` from
    `Z^1`.
  - `[c_n]` is an exact cocycle on `P_𝒰(A)`. By (2) it equals `delta [f_n] + chi`, so along `𝒰` the `c_n` are
    `o(1)`-close to the exact cocycles `delta f_n + chi`. Contradiction.
