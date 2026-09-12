---
rg: 2
id: row2-marked-center-action-return-has-gl8-model
kind: claim
title: The marked-center action return enlarges the prefix chart only to GL8
artifacts:
  - research/row2-marked-center-action-return-gl8-proof.md
  - experiments/row2_marked_center_action_return_gl8_audit.py
distinct_from:
  prefix-order-seven-pair-retains-gl7-mark: that closes both authenticated prefix actors and both order-seven heads in GL7 without making a marked q-center act on either Hecke arm; this adds the literal row-two identity q a_2=a_2 and shows that one new vertex absorbs it.
  literal-selector-roots-force-center-chain: that proves the consecutive q-centers do not preserve the three commuting Pauli cells; this retains only the row-two center, its defining Heisenberg cell, and its action on the actual A_2 occurrence, then gives an exact marked finite model.
  center-chain-common-source-authenticates-native-covariances: that asks for a model-dependent positive cut with unequal source fractions; this is an exact whole-packet occurrence fence and supplies no source-rank typing.
---

**ESTABLISHED MARKED-ACTION FINITE FENCE.**  Retain the authenticated
row-two Hecke triangle

```text
A_2=x_58(a_2),       B_3=x_95(b_3),
a_2=s_1t_00,         b_3=s_000t_1,
[B_3,A_2]=X_2,       (J_2B_3A_2)^7=1.                 (MCA1)
```

The next anchored arm is

```text
A_3=x_69(a_3),       a_3=s_1t_000.
```

It makes the same named `B_3` occurrence into a marked-center cell:

```text
C_3=[A_3,B_3]
   =x_65(a_3b_3)
   =x_65(q),          q=s_1t_1.                       (MCA2)
```

This center acts nontrivially on the actual row-two arm, but its coefficient
action is the identity:

```text
[C_3,A_2]=x_68(qa_2)=x_68(a_2).                       (MCA3)
```

Thus `(MCA3)` is a literal mixed full-coefficient occurrence.  It is not a
prefix covariance or a relation internal to the finite `S_3` actor: it
uses the marked Leavitt identity `qa_2=a_2`.  Let

```text
P=w_65(1)=x_65(1)x_56(1)x_65(1).
```

The returned arm in `(MCA3)` is also the literal constant-Whitehead
transport of the same occurrence:

```text
P A_2 P^(-1)=x_68(a_2)=[C_3,A_2].                    (MCA4)
```

Finally a fixed constant Weyl word `K` carrying the root `(1,3)` to
`(6,5)` gives

```text
K x_13(q) K^(-1)=C_3,                                (MCA5)
```

so the center in `(MCA3)` is the marked coefficient occurrence rather than
an anonymous transvection.

Despite this mixed typing, the union of `(MCA1)--(MCA5)` with the coupled
`J_1,J_2` prefix packet has an exact marked model in `GL_8(F_2)`.  Extend
the seven-vertex chart by one vertex `u` and keep

```text
A_2=e_(10,8_0),       B_3=e_(9,10),
J_2=(8_0 9).
```

Assign

```text
A_3=e_(u,9),           C_3=e_(u,10),
x_68(a_2)=e_(u,8_0),   P=(u 10).                     (MCA6)
```

Then `(MCA2)--(MCA4)` are the standard three-vertex transvection and
Whitehead identities on `(u,10,8_0)`.  Put the old marked child on the
disjoint pair `(7_1,8_1)` and take `K` to exchange that ordered pair with
`(u,10)`; `(MCA5)` holds and the marked child remains nonidentity.  The
new constant swap is disjoint from `J_1,J_2,A_1,B_2`, while its interactions
with `A_2,B_3,A_3` are exactly the displayed root-position interactions.

Consequently the first marked-center action return kills neither row-two
holonomy nor the marked atom.  It enlarges the finite actor chart by one
vertex.  A live next occurrence must compare this returned `A_2` arm with a
second independently typed row-two occurrence on the **same** carrier, or
make the marked-center action close a cycle that cannot be realized by this
three-vertex extension.  Merely using `qa_2=a_2` once is below the finite-
model firewall.

This is a scoped model of the displayed ordinary-root occurrence table,
not a representation of the full binary Leavitt elementary group.  The
calculation is in the elementary image and makes no assertion about a
central Steinberg lift.  No Property T, Kazhdan input, trace assumption,
literature theorem, local computation, or Lean compilation is used.

DERIVATION
row2-marked-center-action-return-gl8-proof

