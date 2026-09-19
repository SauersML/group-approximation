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
root, and

```text
P=M bar M M=w_96(1).
```

This ordinary Whitehead swaps root vertices `6,9`.  Therefore

```text
PB'P=x_89(s_00),       PAP=x_67(t_0).
```

The paths `8->9->7` and `8->6->7` now give the two literal factorizations

```text
[PB'P,A]=[B',PAP]=x_87(s_00t_0)=X_1.                 (1)
```

Only ordinary nonopposite root commutators occur in `(1)`.  For
completeness, the
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

Because `P` and `J_1` have disjoint root vertices, they commute.  Thus the
`J_1` conjugate of the first factorization in `(1)` is the second natural
factorization

```text
[Px_76(s_0)P,x_98(t_00)]=[x_79(s_0),x_98(t_00)]=Y_1. (6)
```

Together `(5)--(6)` close both sides of the returned-root square and prove
`J_1X_1J_1=Y_1`.  The definition
of the native partial Whitehead is the additional literal relation
`J_1=X_1Y_1X_1`.

The auxiliary opposite constant root is also an output of the named arm
packet rather than an untyped completion:

```text
[PA'P,PB'P]=P[A',B']P=x_69(1)=bar M.                 (7)
```

Together with `M=[A',B']=x_96(1)`, equation `(7)` types the literal
returned-root Whitehead `P=M bar M M`.

In the existing seven-coordinate model, write `e_ab=I+E_ab`.  The new
assignments are

```text
bar M=e_(6,9),       P=(6 9),
PAP=e_(6,7_0),       PB'P=e_(8_0,9),
X_1=e_(8_0,7_0),    PA'P=e_(6,8_0),
PBP=e_(7_0,9),       Y_1=e_(7_0,8_0).                 (8)
```

All equations `(1)--(7)` are elementary path products, and

```text
e_(8_0,7_0)e_(7_0,8_0)e_(8_0,7_0)=(7_0 8_0).         (9)
```

The previous model sends the scoped actor to `((7_0 8_0),c)` in
`GL_7(F_2) times C_2`, while every factor in `(7)` has central coordinate
zero.  Equation `(9)` and the literal word equation therefore force `c=0`.  Dropping that
coordinate gives an exact `GL_7(F_2)` model of the enlarged table, and the
marked child `e_(7_1,8_1)` remains nonidentity.  The MSI-only artifact
checks the preceding packet, both literal actor factorizations, and mark
survival.
