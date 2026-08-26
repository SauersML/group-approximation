---
rg: 2
id: odd-native-s-factor-return-diamond-gl7-proof
kind: route
title: Return the odd s00t0 factor through x96 and close its native conjugate
target: odd-native-s-factor-return-diamond-has-gl7-model
requires:
  - first-native-diamond-extension-of-cross-return-has-gl7-c2-model
  - non-equivariant-native-diamond-arm-matches-retain-gl7-c2-gauge
  - primitive-native-hecke-relators-have-no-odd-mixed-occurrence
  - outer-root-leavitt-table
---

The first native return diamond already contains

```text
A=x_97(t_0),       B'=x_86(s_00),       [A,x_76(s_0)]=x_96(1).
```

Put `bar M=x_69(1)`, the ordinary opposite root to the returned constant
root.  The paths `6->9->7` and `8->6->7` give

```text
[x_69(1),A]=x_67(t_0),
[B',x_67(t_0)]=x_87(s_00t_0)=X_1.                    (1)
```

This uses only the ordinary nonopposite root law.  For completeness, the
`(7,8)` block of the first partial Whitehead is

```text
J_1 = [[1+y_1x_1, y_1], [x_1, 1+x_1y_1]],
x_1=s_00t_0,       y_1=s_0t_00.                       (2)
```

Apply `(2)` on the left to the column `(0,s_00)^t`.  Prefix cancellation
gives `(s_0t_00)s_00=s_0` and
`(1+s_00t_00)s_00=0`, hence

```text
J_1x_86(s_00)J_1=x_76(s_0).                           (3)
```

Apply `(2)` on the right to the row `(t_0,0)`.  Since
`t_0(s_1t_1)=0` and `t_0(s_0t_00)=t_00`, this gives

```text
J_1x_67(t_0)J_1=x_68(t_00).                           (4)
```

Commuting `(3)--(4)` along `7->6->8` yields

```text
[x_76(s_0),x_68(t_00)]=x_78(s_0t_00)=Y_1.            (5)
```

Simultaneous conjugation of `(1)` proves `J_1X_1J_1=Y_1`.  The definition
of the native partial Whitehead is the additional literal relation
`J_1=X_1Y_1X_1`.

In the existing seven-coordinate model, write `e_ab=I+E_ab`.  The new
assignments are

```text
bar M=e_(6,9),       x_67(t_0)=e_(6,7_0),
X_1=e_(8_0,7_0),    x_68(t_00)=e_(6,8_0),
Y_1=e_(7_0,8_0).                                      (6)
```

All equations `(1)--(5)` are elementary path products, and

```text
e_(8_0,7_0)e_(7_0,8_0)e_(8_0,7_0)=(7_0 8_0).         (7)
```

The previous model sends the scoped actor to `((7_0 8_0),c)` in
`GL_7(F_2) times C_2`, while every factor in `(7)` has central coordinate
zero.  The literal word equation therefore forces `c=0`.  Dropping that
coordinate gives an exact `GL_7(F_2)` model of the enlarged table, and the
marked child `e_(7_1,8_1)` remains nonidentity.  The MSI-only artifact
checks the preceding packet together with `(1)--(7)`.

