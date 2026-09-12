---
rg: 2
id: no-s0-lift-from-kernel-unitization-df
kind: route
title: Direct finiteness of the unitized evaluation kernel excludes every left-invertible lift of s_0
target: no-left-invertible-lift-of-s0-in-leavitt-group-algebra
requires:
  - leavitt-evaluation-kernel-unitization-directly-finite
  - leavitt-kaplansky-failures-have-invisible-witnesses
  - leavitt-unit-group-algebra-surjects-onto-leavitt
artifacts:
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

Let `a` lift `s_0` and `b a = 1`. Applying the evaluation to `a b = 1` would make `s_0`
a unit of `R`. It is not, since `t_0 s_0 = 1` would then give `s_1 t_1 = 0` and
`1 = (t_1 s_1)^2 = 0`. So `a b != 1`, and `(a, b)` is a direct-finiteness failure of
`F_2[R^x]`. The second prerequisite turns it into a failure of `K^+`, contradicting the
first. So no lift of `s_0` is left invertible.
