---
rg: 2
id: ternary-swap-fullness-projects-to-anti-invariant-half
kind: route
title: Project the unit-group corner equation to the anti-central summand
target: ternary-anti-invariant-swap-corner-is-full
requires: [ternary-leavitt-swap-idempotent-is-full, ternary-leavitt-swap-problem-splits-at-central-involution]
artifacts:
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Multiply `c e b = 1` by the central idempotent `eps_-`. This gives
`(c eps_-)(e eps_-)(b eps_-) = eps_-`, the anti-central equation with `e_- = e eps_-`. So the
unit-group equation implies both halves, and each half suffices for a counterexample on its own.
