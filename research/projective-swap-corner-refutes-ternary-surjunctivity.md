---
rg: 2
id: projective-swap-corner-refutes-ternary-surjunctivity
kind: route
title: A one-sided inverse on the scalar-quotient summand is a direct-finiteness failure of the whole group algebra
target: ternary-leavitt-unit-group-nonsurjunctive
requires: [projective-ternary-swap-idempotent-is-full, ternary-leavitt-swap-problem-splits-at-central-involution, stable-finiteness-failure-refutes-surjunctivity]
artifacts:
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

`S_+ = eps_+ F_3[G] ~= F_3[PG]` is a central summand.
* From `c ebar b = eps_+` in `S_+`, put `A = ebar b + eps_-` and `C = c + eps_-`, so `CA = 1`.
* If `AC = 1`, then `ebar` is right invertible in `S_+`, hence `ebar = eps_+`, which forces
  `wbar = 1`. That is false.
* So `F_3[G]` is not directly finite, and `stable-finiteness-failure-refutes-surjunctivity`
  refutes surjunctivity of `G` on the full shift.

This complements `projective-swap-corner-gives-strict-automaton`, which gives a strict automaton
over `PG` itself.
