---
rg: 2
id: v-augmentation-from-minus-one-gate-and-extension
kind: route
title: The minus-one gate plus extension of detecting V rank functions forces every rank function on F_3[V] to be the augmentation
target: thompson-v-ternary-rank-functions-are-augmentation
requires:
  - sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one
  - v-detecting-rank-functions-extend-to-ternary-leavitt-units
  - simple-group-rank-functions-are-augmentation-or-detecting
artifacts:
  - research/artifacts/ternary-minus-one-gate-outside-signed-thompson-2026-09-12.md
---

Suppose `F_3[V]` carried a rank function other than the augmentation. `V` is simple, so by the dichotomy it is
detecting. By the extension claim `F_3[G_3]` would then carry a rank function with `rk(1 - [z]) > 0`,
contradicting the minus-one gate. Hence every rank function on `F_3[V]` is the augmentation.

Together with `ternary-units-kill-minus-one-via-thompson-v-augmentation`, this makes the minus-one gate and the
V gate equivalent, conditional on the open extension claim. This route is conditional and establishes nothing
by itself.
