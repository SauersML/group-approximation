---
rg: 2
id: row2-marked-center-action-return-gl8-proof
kind: route
title: Compile the row-two marked-center action and audit its one-vertex extension
target: row2-marked-center-action-return-has-gl8-model
requires:
  - prefix-order-seven-pair-retains-gl7-mark
  - literal-selector-roots-force-center-chain
  - outer-root-leavitt-table
---

Put `a_2=s_1t_00`, `a_3=s_1t_000`, `b_3=s_000t_1` and
`q=s_1t_1`.  Prefix cancellation gives

```text
a_3b_3=q,              qa_2=a_2.                       (1)
```

For

```text
A_2=x_58(a_2),       A_3=x_69(a_3),       B_3=x_95(b_3)
```

the ordinary nonopposite Steinberg commutator law gives

```text
C_3=[A_3,B_3]=x_65(q),
[C_3,A_2]=x_68(a_2).                                   (2)
```

The constant Whitehead `P=w_65(1)` exchanges root indices `6,5`, hence

```text
P A_2 P^(-1)=x_68(a_2).                                (3)
```

A constant Weyl word carrying `(1,3)` to `(6,5)` conjugates the marked
root to `C_3` in the elementary image.

For the finite model retain the eight matrices of the coupled prefix and
order-seven packet and add one vertex `u`.  Set

```text
A_3=e_(u,9),       C_3=e_(u,10),
x_68(a_2)=e_(u,8_0),       P=(u 10).                   (4)
```

Since `B_3=e_(9,10)` and `A_2=e_(10,8_0)`, equations `(2)--(3)` are exact.
The old mark is `e_(7_1,8_1)`; a permutation exchanging
`(7_1,8_1)` with `(u,10)` implements the required marked-root conjugacy.
The MSI-only audit checks the coupled prefix braid, both order-seven heads,
the marked-center cell and action return, the factorization of `P`, its
commutations with the disjoint first-row packet, and survival of the mark.

