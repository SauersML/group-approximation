---
rg: 2
id: prefix-order-seven-pair-gl7-proof
kind: route
title: Fold both odd Hecke heads into the authenticated prefix triangle
target: prefix-order-seven-pair-retains-gl7-mark
requires:
  - literal-prefix-coupling-of-j1-j2-has-gl7-model
  - native-whitehead-hecke-head-has-order-seven-anchor
  - quarter-whiteheads-lack-unequal-source-conjugacy
---

Use the occurrence assignment `(P73)`.  The paths

```text
8_0 -> 6 -> 7_0,          9 -> 10 -> 8_0
```

give

```text
[B_2,A_1]=e_(8_0,7_0)=X_1,
[B_3,A_2]=e_(9,8_0)=X_2.                              (1)
```

The matrices `J_i` are the two adjacent transpositions.  Multiplication of
the three-by-three blocks shows

```text
(J_1B_2A_1)^7=1,       (J_2B_3A_2)^7=1.              (2)
```

These are two standard `GL_3(F_2)` order-seven cells sharing the vertex
`8_0`.  The MSI-only artifact checks `(1)--(2)`, the adjacent braid, and
survival of the old marked child.  Hence simultaneous order-seven
authentication supplies no unequal selector rank typing.
