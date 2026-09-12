---
rg: 2
id: simple-kazhdan-hyperlinear-from-leavitt-unit-group
kind: route
title: A hyperlinear binary Leavitt unit group is an infinite simple hyperlinear Kazhdan group
target: infinite-simple-kazhdan-hyperlinear-group
requires: [binary-leavitt-unit-group-hyperlinear, openai-nine-leaf-leavitt-configuration, leavitt-gl-equals-el-and-perfect-unit-group, binary-leavitt-elementary-group-is-simple]
---

Put `R=L_(F_2)(1,2)` and `H=R^x`.

- **Property (T).** `openai-nine-leaf-leavitt-configuration` gives a Kazhdan
  group `G=EL_D(R) ~= EL_9(R)`, by Ershov--Jaikin-Zapirain, and records
  `G=R^x`. The in-repository identification is
  `leavitt-gl-equals-el-and-perfect-unit-group`: `GL_n(R)=EL_n(R)` at every
  rank, and the prefix code `D` identifies `R` with `M_9(R)`, so
  `R^x=GL_1(R)~=GL_9(R)=EL_9(R)`.
- **Infinite and simple.** By the same self-similarity, `H~=GL_n(R)=EL_n(R)`
  for every `n>=2`. `binary-leavitt-elementary-group-is-simple` makes
  `EL_n(R)` simple for all sufficiently large `n`. `H` contains Thompson's
  `V`, so it is infinite.
- **Hyperlinear.** This is the premise `binary-leavitt-unit-group-hyperlinear`.

So `H` witnesses the target. The implication runs one way only: a proof that
`H` is not hyperlinear would say nothing about other infinite simple Kazhdan
groups.
