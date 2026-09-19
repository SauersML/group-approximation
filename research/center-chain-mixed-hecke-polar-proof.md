---
rg: 2
id: center-chain-mixed-hecke-polar-proof
kind: route
title: Multiply the four Hecke orbit averages and polarize the two mixed maps
target: center-chain-mixed-hecke-polars-share-a1-tail
requires:
  - center-chain-four-hecke-flags-have-native-ranks
  - literal-selector-roots-force-center-chain
---

Use the affine orbit averages

```text
D_1=<d>,               D_2=<f,k>,
W_1=<v,w>,             W_2=<v,w,s>.
```

The four Hecke operators are

```text
eB_2z_(D_1), eB_3z_(D_2), eA_1z_(W_1), eA_2A_1z_(W_2). (1)
```

Every orbit average in `(1)` is `H`-invariant and therefore commutes with
`e`.  The root groups `D_1` and `W_1` commute elementwise, as do `D_2` and
`A_2`.  Hence

```text
M_1=eB_2A_1 z_<d,v,w>.                                 (2)
```

For the second row, `A_1` conjugates `f` to `fc` and fixes `k`, while
`D_2` commutes with `A_2`.  Therefore

```text
z_(D_2)A_2A_1=A_2A_1z_<fc,k>,
M_2=eB_3A_2A_1z_<fc,k,v,w,s>.                          (3)
```

The groups in `(2)--(3)` are elementary abelian.  They are normalized by
`H`: on the second group the only nontrivial center-chain action sends
`f` to `fk` and fixes `c`, hence sends `fc` to `(fc)k`; the A-arm span is
already `H`-stable.  Thus `e` commutes with both subgroup averages.

For any group element `g` and subgroup average `z_K`,

```text
(gz_K)^*(gz_K)=z_K.
```

Applying this identity to `(2)--(3)`, and using the commutation with `e`,
gives `M_i^*M_i=ez_(K_i)`.  Independence of the displayed root coordinates
gives `|K_1|=8`, `|K_2|=32`, so the stated support traces follow.

Finally all named roots are involutions.  Thus
`(B_2A_1)^2=[B_2,A_1]`.  Since `A_1` commutes with `B_3,A_2`,

```text
(B_3A_2A_1)^2=(B_3A_2)^2=[B_3,A_2].
```

The elementary commutator formula gives the two roots in `(MHP7)`.
