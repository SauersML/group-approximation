---
rg: 2
id: thompson-v-binary-df-failure-ascends-to-leavitt-units
kind: route
title: A full averaging idempotent in F_2[V] makes the binary Leavitt unit group algebra not directly finite
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - thompson-v-order-three-averaging-idempotent-is-full
  - leavitt-surjunctivity-tower
---

`leavitt-surjunctivity-tower` gives `V <= R^x = L_(F_2)(1,2)^x`, so `F_2[V]` is a unital
subalgebra of `F_2[R^x]`. The equation `c e_h b = 1` and the inequality `e_h != 1` hold there
too. Proposition 2.2 of the artifact then gives `d a = 1 != a d` in `F_2[R^x]`.
