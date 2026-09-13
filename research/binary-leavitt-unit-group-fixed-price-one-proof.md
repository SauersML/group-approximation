---
rg: 2
id: binary-leavitt-unit-group-fixed-price-one-proof
kind: route
title: The unit group is E_3 over the Leavitt algebra, which is countably infinite
target: binary-leavitt-unit-group-has-fixed-price-one
requires: [elementary-groups-over-infinite-rings-have-fixed-price-one, leavitt-gl-equals-el-and-perfect-unit-group]
---

- The three-leaf prefix code gives `L^x ≅ GL_3(L)`, and `GL_3(L) = E_3(L)`
  (`leavitt-gl-equals-el-and-perfect-unit-group`).
- `L = L_(F_2)(1,2)` is countable, and infinite because distinct positive words are distinct.
- Apply the elementary-group criterion with `n = 3`.
