---
rg: 2
id: binary-leavitt-pbh-via-chen-module-lines
kind: route
title: Take p = 2 in the Chen-module line action, where the scalar group is trivial
target: binary-leavitt-unit-group-satisfies-pbh
requires:
  - leavitt-unit-groups-mod-scalars-satisfy-pbh
---

Over `F_2` we have `F_2^× = 1`, so `G_2 = L_(F_2)(1,2)^× = U`. By
`leavitt-unit-groups-mod-scalars-satisfy-pbh`, `U` itself acts with type (A) on the
lines, equivalently the nonzero vectors, of `F_2[D]`.

This route is independent of `leavitt-pbh-via-cantor-module-affine-actor`. It does not
use `leavitt-cantor-module-semidirect-product-is-fp`. `∎`
