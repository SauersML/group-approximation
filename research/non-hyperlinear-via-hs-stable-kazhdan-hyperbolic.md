---
rg: 2
id: non-hyperlinear-via-hs-stable-kazhdan-hyperbolic
kind: route
title: Flexible HS-stability of one Kazhdan hyperbolic group with b_2 >= 1 gives an explicit-shape non-hyperlinear group
target: non-hyperlinear-group
requires: [kazhdan-hyperbolic-hs-stability-kills-hyperlinearity, kazhdan-hyperbolic-b2-group-flexibly-hs-stable]
---

## Why sufficient

`kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` turns the premise into a
non-hyperlinear finite central extension of the stable group. The output is
hyperbolic, which no other stability route into this goal provides. The
`SL_2(Z[1/p])` and `Sp_(2g)(Z)` routes produce non-residually-finite arithmetic
extensions that contain `Z^2`.
