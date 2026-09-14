---
rg: 2
id: f3-linear-soficity-refutes-projective-swap-fullness
kind: route
title: Linear soficity over F_3 makes the group algebra directly finite, which no full proper idempotent allows
target: projective-ternary-swap-idempotent-is-not-full
requires: [projective-ternary-group-is-f3-linear-sofic, linear-sofic-group-algebra-is-stably-finite]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

Suppose `c ebar b = 1` and put `x = ebar b`, `y = c`. Then `y x = 1`, while `x y` lies
in `ebar F_3[PG]`. That right ideal does not contain `1`: `1 = ebar z` would give
`ebar = ebar ebar z = ebar z = 1`, and `wbar != 1`. So `x y != 1`, and `F_3[PG]` is
not directly finite. If `PG` is `F_3`-linear sofic, `F_3[PG]` is stably finite, a
contradiction. The same argument refutes `projective-ternary-klein-idempotent-is-full`,
since a full `e_K` makes `ebar` full.
