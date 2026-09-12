---
rg: 2
id: reverse-return-native-arm-leavitt-diamond-proof
kind: route
title: Factor the two spectator returns through the literal center-chain arms and conjugate by the native Whiteheads
target: reverse-return-has-native-arm-leavitt-diamond
requires:
  - reverse-mixed-root-has-two-positive-hecke-commutator-returns
  - native-whitehead-hecke-head-has-order-seven-anchor
---

For row one, the ordinary nonopposite Steinberg commutator law and prefix
cancellation give

```text
[x_94(t_1),x_47(s_1t_0)]=x_97(t_1s_1t_0)=x_97(t_0),
[x_97(t_0),x_76(s_0)]=x_96(t_0s_0)=x_96(1).           (1)
```

On the other side,

```text
[x_84(s_00t_1),x_46(s_1)]=x_86(s_00),
[x_98(t_00),x_86(s_00)]=x_96(t_00s_00)=x_96(1).       (2)
```

The actual block for `J_1` on `(7,8)` is the prefix Whitehead for the
partial inverse pair

```text
x_1=s_00t_0,                   y_1=s_0t_00.
```

Its standard root conjugation formula, followed by the same prefix
cancellations, gives

```text
J_1x_97(t_0)J_1=x_98(t_00),
J_1x_76(s_0)J_1=x_86(s_00).                            (3)
```

Equations `(1)--(3)` are `(RND2)--(RND3)`.  Notice that both appearances of
`A_1,B_2,J_1` are the literal words from `(OWH1)`; no analytic label
reflection or auxiliary completion has been substituted.

For row two, replace the partial inverse pair by

```text
x_2=s_000t_00,                 y_2=s_00t_000.
```

Then

```text
[x_25(t_1),x_58(s_1t_00)]=x_28(t_00),
[x_28(t_00),x_87(s_00)]=x_27(1),
[x_95(s_000t_1),x_57(s_1)]=x_97(s_000),
[x_29(t_000),x_97(s_000)]=x_27(1),                    (4)
```

and Whitehead conjugation gives

```text
J_2x_28(t_00)J_2=x_29(t_000),
J_2x_87(s_00)J_2=x_97(s_000).                         (5)
```

This proves `(RND4)--(RND5)`.  The MSI artifact verifies all root-word
equalities as exact `7 by 7` elementary matrices over the faithful binary
prefix normal form, including both Whitehead conjugations.  The proof is
also immediate from the displayed Steinberg relations, so no exhaustive
search or numerical tolerance is involved.

Finally, simultaneous conjugation preserves a commutator.  Thus the two
factorizations in each row form a naturality diamond; that observation is
why the result is recorded as a native occurrence attachment, rather than
as an already established same-chart multiplicity-gauge identity.
