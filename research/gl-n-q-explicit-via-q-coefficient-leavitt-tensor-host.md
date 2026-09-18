---
rg: 2
id: gl-n-q-explicit-via-q-coefficient-leavitt-tensor-host
kind: route
title: A named finitely presented central simple Q-ring B gives the finitely presented overgroup (B ⊗ L_Q(1,2))^x of GL_n(Q)
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - fp-central-simple-q-ring-with-trivial-leavitt-k-theory
  - q-coefficient-leavitt-tensor-unit-groups-are-fp
---

Take `B` from `fp-central-simple-q-ring-with-trivial-leavitt-k-theory` and put
`R = B ⊗_Q L_Q(1,2)`.
- By `q-coefficient-leavitt-tensor-unit-groups-are-fp`, `R^x` is finitely presented and
  contains `GL_n(Q)` for every `n`.
- `R^x` is the unit group of a named ring. That is the kind of construction
  `gl-n-q-explicit-natural-fp-overgroup` counts as natural, provided `B` itself is
  explicit.

This route does **not** reach `gl-n-q-embeds-in-fp-simple-group`. The simple quotient
`R^x / Q^x` is not finitely presented, by the scalar obstruction recorded in
`q-coefficient-leavitt-tensor-unit-groups-are-fp`.
