---
rg: 2
id: thompson-v-has-no-rigid-compression-defect-proof
kind: route
title: Apply the a-T-menable defect theorem to Farley's Haagerup property for V
target: thompson-v-has-no-rigid-compression-defect
requires:
  - thompson-v-has-haagerup-property
  - a-t-menable-groups-have-no-rigid-compression-defect
---

`V` has the Haagerup property (`thompson-v-has-haagerup-property`). Apply
`a-t-menable-groups-have-no-rigid-compression-defect` with `L = V` and any
ambient `H` containing `V`. That gives finiteness of `G`, normality of `Gamma`
and the trivial defect.

For the cylinder computation in the claim: `t` maps `0*`, `10*`, `11*` to
`00*`, `01*`, `1*`. So `t` maps the complement `1*` of `0*` onto `01* u 1*`,
and conjugation by `t` sends `V_(0*)` onto `V_(00*)` and `V_(1*)` onto
`V_(01* u 1*)`. Take `z = (10 11)` in `V_(1*)`. Then `t z t^-1 = (01 1)`, whose
support meets `0*` in `01*`. For `gamma = (00 01)` in `V_(0*)`,
`(01 1)` and `(00 01)` share the cylinder `01*`, so they do not commute, and
`[t z t^-1, gamma] != 1`. ∎
