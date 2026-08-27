---
rg: 2
id: native-a1-b2-hecke-triangle-gl7-proof
kind: route
title: Compile the first center-chain triangle through the returned prefix arms
target: native-a1-b2-hecke-triangle-has-gl7-model
requires:
  - literal-prefix-coupling-of-j1-j2-has-gl7-model
  - odd-native-s-factor-return-diamond-has-gl7-model
  - native-whitehead-hecke-head-has-order-seven-anchor
  - outer-root-leavitt-table
---

The named returned-prefix occurrences have coefficients `t_0` and `s_00`.
Adjoining `S_1=x_49(s_1)` and `T_1=x_94(t_1)`, the two compatible root
paths give

```text
[S_1,x_97(t_0)]=x_47(s_1t_0)=A_1,
[x_89(s_00),T_1]=x_84(s_00t_1)=B_2.                 (1)
```

Since `t_1s_1=1`, a third ordinary root commutator gives

```text
[B_2,A_1]
 =x_87((s_00t_1)(s_1t_0))
 =x_87(s_00t_0)=X_1.                                (2)
```

The literal relation `J_1=X_1Y_1X_1` therefore types `J_1` against the
actual first center-chain triangle.  The established three-summand block
calculation gives `(J_1B_2A_1)^7=1`.

For the finite model use the existing GL7 chart and the assignments

```text
x_97(t_0)=e_(9,7_0),      x_89(s_00)=e_(8_0,9),
S_1=e_(6,9),              T_1=e_(9,6).
```

Equations `(1)--(2)` force

```text
A_1=e_(6,7_0),            B_2=e_(8_0,6),
X_1=e_(8_0,7_0).
```

Together with `J_1=(7_0 8_0)`, these are the standard transvection,
transvection, swap generators on a three-dimensional binary space.  Direct
multiplication gives exact order seven for `J_1B_2A_1`.  All previously
displayed `J_1,J_2` prefix rows remain unchanged, and the marked child on
the disjoint second branch survives.  The MSI-only audit verifies these
matrix equalities and the exact order.

