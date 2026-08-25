---
rg: 2
id: center-chain-mixed-hecke-polars-share-a1-tail
kind: claim
title: The mixed source-target Hecke polars have literal selector squares and a common A1 tail
artifacts:
  - research/center-chain-mixed-hecke-polar-proof.md
distinct_from:
  center-chain-four-hecke-flags-have-native-ranks: that computes the four source and target support ranks separately; this computes the two source-to-target cross-Grams and their exact polar words.
  native-whitehead-corner-collapses-hecke-flags: that compresses the two full native Whitehead involutions to one common reducing corner and makes the A-side flags equal; this keeps rectangular source and range supports and uses the literal commutator square roots instead.
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that forbids a fixed exact complete occurrence row; the identities here stop before occurrence typing and expose the remaining noncommuting-tail obstruction.
---

**ESTABLISHED MIXED-POLAR NORMAL FORMS.**  Let the four Hecke partial
isometries be those of `center-chain-four-hecke-flags-have-native-ranks`, and
form the source-to-target cross-Grams

```text
M_1=(eB_2e)^*(eA_1e),
M_2=(eB_3e)^*(eA_2A_1e).                               (MHP1)
```

With

```text
d=x_82(b_2),
v=x_57(a_1), w=x_67(a_1), s=x_68(a_2),
f=x_94(b_3), k=x_92(b_3), c=x_97(b_3a_1),              (MHP2)
```

put

```text
K_1=<d,v,w>,
K_2=<fc,k,v,w,s>.                                      (MHP3)
```

These are `H`-invariant elementary abelian groups of orders `8` and `32`.
The exact polar normal forms are

```text
M_1=e(B_2A_1)z_(K_1),
M_2=e(B_3A_2A_1)z_(K_2),                               (MHP4)
M_i^*M_i=e z_(K_i).                                    (MHP5)
```

Thus the source-support masses of the mixed maps relative to `e` are
`1/8` and `1/32`.  Their polar words share a literal right tail:

```text
B_2A_1=(B_2)A_1,             B_3A_2A_1=(B_3A_2)A_1.  (MHP6)
```

Moreover their squares are exactly the two literal selector roots,

```text
(B_2A_1)^2=[B_2,A_1]=x_87(s_(00)t_0),
(B_3A_2A_1)^2=[B_3,A_2]=x_98(s_(000)t_(00)).           (MHP7)
```

The second equality uses that `A_1` commutes with both `B_3` and `A_2`.
This supplies an exact algebraic interface between the four Hecke flags and
the two native coefficient roots.

It is not yet a typed occurrence row.  In the first polar word the proposed
tail fails to separate from its leading factor:

```text
[B_2,A_1]=x_87(s_(00)t_0) !=1,
```

whereas `[B_3A_2,A_1]=1`.  Hence the common `A_1` suffix cannot simply be
declared a common multiplicity gauge: its commutator in the first row is
precisely the first selector root.  The remaining problem is quantitative
finite-matrix row typing, not another fixed group-algebra restriction.

DERIVATION
center-chain-mixed-hecke-polar-proof

