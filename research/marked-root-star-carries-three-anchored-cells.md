---
rg: 2
id: marked-root-star-carries-three-anchored-cells
kind: claim
title: A positive marked carrier supports three q-anchored Heisenberg cells
artifacts:
  - research/three-anchored-root-cells-proof.md
distinct_from:
  e5-idempotent-root-has-two-pair-extraspecial-cell: that builds two Pauli pairs with one common central root and one idempotent coefficient; this uses three distinct but jointly positive central-root carriers and records the three q-anchored prefix factorizations whose cross-products are the two native scale arrows.
  binary-leavitt-native-two-scale-cross-gram-positive: that must authenticate the cross-products as the actual selector transports; this puts all six anchored arm occurrences on one fixed positive carrier but does not perform that occurrence identification.
---

In the notation of `seventeen-root-star-has-marked-triple-overlap`, put

```text
F=P Q_4 Q_5 Q_6.
```

Then

```text
tau(F) >= (11/1360)tau(P).                              (ARC1)
```

For `m=1,2,3`, define the binary-prefix coefficients

```text
a_m=s_1 t_(0^m),                 b_m=s_(0^m)t_1.       (ARC2)
```

On `FH`, the following three Steinberg pairs are mutually cross-commuting
and have central commutator `-1`:

```text
A_1=x_47(a_1),   B_1=x_72(b_1),   [A_1,B_1]=x_42(q),
A_2=x_58(a_2),   B_2=x_82(b_2),   [A_2,B_2]=x_52(q),
A_3=x_69(a_3),   B_3=x_92(b_3),   [A_3,B_3]=x_62(q).   (ARC3)
```

Thus they generate the standard three-qubit Pauli factor `M_8(C)` tensored
with a multiplicity reservoir on `FH`.  The coefficients simultaneously
satisfy

```text
a_m b_m=q,                 b_m a_m=e_m=s_(0^m)t_(0^m),
b_(m+1)a_m=s_(0^(m+1))t_(0^m)             (m=1,2).     (ARC4)
```

The last two cross-products in `(ARC4)` are exactly the depth-one-to-two and
depth-two-to-three native prefix transports.  This is a common positive
carrier for all three anchored arm cells, not yet a proof that the group-word
occurrences representing those two cross-products reduce `F` or equal the
selector transports there.

DERIVATION
three-anchored-root-cells-proof
