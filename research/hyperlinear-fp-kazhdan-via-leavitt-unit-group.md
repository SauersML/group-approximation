---
rg: 2
id: hyperlinear-fp-kazhdan-via-leavitt-unit-group
kind: route
title: A hyperlinear binary Leavitt unit group is a finitely presented simple hyperlinear Kazhdan group
target: hyperlinear-fp-infinite-simple-kazhdan-group
requires: [binary-leavitt-unit-group-hyperlinear, leavitt-unit-group-finitely-presented, openai-nine-leaf-leavitt-configuration, leavitt-gl-equals-el-and-perfect-unit-group, binary-leavitt-elementary-group-is-simple]
---

Put `R = L_(F_2)(1,2)` and `H = R^x`.
- **Infinite, simple and Kazhdan.** This is the argument of
  `simple-kazhdan-hyperlinear-from-leavitt-unit-group`, from the same four inputs:
  - `openai-nine-leaf-leavitt-configuration` together with
    `leavitt-gl-equals-el-and-perfect-unit-group` identifies `H` with a Kazhdan elementary group;
  - `binary-leavitt-elementary-group-is-simple` makes it simple;
  - `H` contains Thompson's `V`, so it is infinite.
- **Finitely presented.** `leavitt-unit-group-finitely-presented` (Khanh, arXiv:2609.08428v1,
  Theorem 6.1).
- **Hyperlinear.** This is the premise `binary-leavitt-unit-group-hyperlinear`.

Only the hyperlinear form of the target can come from this route: `H` is nonsofic
(`openai-leavitt-unit-nonsofic`).
