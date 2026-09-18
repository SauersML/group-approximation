---
rg: 2
id: odometer-factor-via-smart-level-zero-return-map
kind: route
title: The induced SMART element of 2V is a witness with k = 2 and m = 3
target: some-brin-thompson-element-factors-onto-an-odometer
requires:
  - smart-level-zero-return-map-factors-onto-3-adic-odometer
---

Take `k = 2`, `m = 3`, `T = U ∈ 2V` from
`smart-level-zero-return-map-factors-onto-3-adic-odometer`. The factor map is
`C^2 -> Y -> Z/2 × Z_3 -> Z_3`: the inverse of the brick-local conjugacy and
the coding, then `π`, then the projection. It is continuous and surjective, and
it intertwines `U` with `+1` because the projection is a homomorphism sending
`(1,1)` to `1`.
