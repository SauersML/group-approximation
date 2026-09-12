---
rg: 2
id: thompson-v-direct-finiteness-failure-from-swap-fullness
kind: route
title: A full proper idempotent gives a one-sided unit in the ternary group algebra of V
target: thompson-v-modular-group-algebra-not-directly-finite
requires:
  - thompson-v-ternary-swap-idempotent-is-full
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

Proposition 2.2 of the artifact, at `p = 3`. From `c e b = 1` with `e = 2(1+w) != 1`, put
`a = e b` and `d = c e`.
- `d a = c e b = 1`.
- `(1-e) a = (1-e) e b = 0`. So if `a d = 1`, then `1 - e = (1-e) a d = 0`, which is false.
So `a d != 1`.
