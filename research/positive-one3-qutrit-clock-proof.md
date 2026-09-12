---
rg: 2
id: positive-one3-qutrit-clock-proof
kind: route
title: Identify the three zero positions of an affine Z3 clock orbit
target: positive-one3-is-one-qutrit-clock-context
requires: []
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
---

The affine equations `h_y=h_x-1` and `h_z=h_x+1` have the three solutions

```text
(0,2,1), (1,0,2), (2,1,0).
```

Declaring a Boolean coordinate true exactly at hidden value zero gives
`100,010,001`.  Spectral functional calculus translates this table to
`(QOC1)`.  Replacing the scalar phase `omega` by the central letter `J`
gives `(QOC2)`, and comparing the truth projection of two occurrences gives
`(QOC3)`.

