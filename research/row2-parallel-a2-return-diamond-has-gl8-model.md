---
rg: 2
id: row2-parallel-a2-return-diamond-has-gl8-model
kind: claim
title: The independently factored row-two return still closes in GL8
artifacts:
  - research/row2-parallel-a2-return-diamond-gl8-proof.md
  - experiments/row2_parallel_a2_return_diamond_gl8_audit.py
distinct_from:
  row2-marked-center-action-return-has-gl8-model: that compares the marked-center output with the constant-Whitehead transport of A_2 but does not independently factor either coefficient occurrence; this adds both literal s_1,t_00 paths and their complete constant-Weyl comparison.
  reverse-return-has-native-arm-leavitt-diamond: that returns a constant spectator through two prefix factorizations; this returns the actual nonzero-degree coefficient a_2=s_1t_00 and shares it with the marked-center action.
  center-chain-common-source-authenticates-native-covariances: that asks for unequal source-rank typing on a model-dependent positive cut; this is a whole-packet root-occurrence fence with no Hecke source projection.
---

**ESTABLISHED PARALLEL-PATH FINITE FENCE.**  Keep the row-two marked-center
action packet

```text
A_2=x_58(a_2),       C_3=x_65(q),
R=[C_3,A_2]=x_68(a_2),       a_2=s_1t_00,              (PAD1)
```

and its constant-Whitehead comparison

```text
P=w_65(1),            P A_2 P^(-1)=R.                 (PAD2)
```

The native `A_2` occurrence itself has a literal coefficient factorization

```text
S_57=x_57(s_1),       T_78=x_78(t_00),
[S_57,T_78]=A_2.                                      (PAD3)
```

Conjugating this entire path by `P` gives

```text
S_67=P S_57 P^(-1)=x_67(s_1),
[S_67,T_78]=R.                                        (PAD4)
```

There is also an independently rooted factorization of the same returned
coefficient:

```text
S_69=x_69(s_1),       T_98=x_98(t_00),
[S_69,T_98]=R.                                        (PAD5)
```

These are not merely two analytically equal outputs.  The constant
Whitehead

```text
Q=w_79(1)
```

compares the factors occurrence by occurrence:

```text
Q S_67 Q^(-1)=S_69,
Q T_78 Q^(-1)=T_98,
Q R Q^(-1)=R.                                         (PAD6)
```

Thus `(PAD1)--(PAD6)` give the sharp literal comparison requested after the
first marked-center fence: the native `A_2` arm, its marked-center return,
and a second coefficient factorization of that return all live in one
ordinary-root diagram.

The full diagram nevertheless extends the same `GL_8(F_2)` marked model.
Using the vertices of the preceding fence, assign

```text
S_57=e_(10,7_0),       T_78=e_(7_0,8_0),
S_67=e_(u,7_0),        S_69=e_(u,9),
T_98=e_(9,8_0),        Q=(7_0 9).                    (PAD7)
```

The first path gives `A_2=e_(10,8_0)`, while the other two give
`R=e_(u,8_0)`.  The old `P=(u 10)` and new `Q=(7_0 9)` conjugate every
displayed factor exactly.  In particular, the model may identify the
separately named `x_78(t_00)` with the old `Y_1` transvection and
`x_98(t_00)` with the old `X_2` transvection: no displayed coefficient sum
or source projection distinguishes those same-root occurrences.  The
marked child remains the nonidentity transvection on `(7_1,8_1)`.

Therefore even a complete two-path root comparison does not kill row-two
holonomy.  It only adds another finite root-position square.  A live next
occurrence must prevent the same-root coefficient identifications used in
`(PAD7)`, for example by placing `x_78(t_00)` and `Y_1=x_78(s_0t_00)` in
one additive/multiplicative coefficient row attached to the marked carrier,
or by coupling the returned `A_2` occurrence directly to the unequal Hecke
source projection.  Another constant-Weyl path comparison remains inside
the finite `GL_8` closure.

This is a scoped model of the displayed ordinary-root occurrence table,
not a representation of the full binary Leavitt elementary group.  The
calculation is in the elementary image and makes no assertion about a
central Steinberg lift.  No Property T, Kazhdan input, trace assumption,
literature theorem, local computation, or Lean compilation is used.

DERIVATION
row2-parallel-a2-return-diamond-gl8-proof

