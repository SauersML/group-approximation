---
rg: 2
id: two-same-pair-mixed-braid-native-target-proof
kind: route
title: Separate the complementary right supports in both two-root orders
target: two-same-pair-roots-cannot-return-mixed-braid-native-chart
requires:
  - one-elementary-root-cannot-return-mixed-braid-native-chart
---

In the ordered basis `(e_7,e_9)`, write

```text
U(a)=[[1,a],[0,1]],       L(b)=[[1,0],[b,1]],
P e_7=(q_0,q_1)^t.                                      (1)
```

Two upper roots or two lower roots combine by root additivity, so the
one-root claim applies.  It remains to treat the two opposite orders.

First,

```text
U(a)L(b)=[[1+ab,a],[b,1]],
U(a)L(b)P e_7=((1+ab)q_0+aq_1, bq_0+q_1)^t.           (2)
```

The second coordinate in `(2)` is nonzero.  Indeed, if `bq_0+q_1=0`,
right multiplication by `q_1` and the orthogonality
`q_0q_1=0`, `q_1^2=q_1` give `q_1=0`, a contradiction.  Since `J` fixes
`e_9`, the vector cannot land in `F_1` after applying `J`.

For the other order,

```text
L(b)U(a)=[[1,a],[b,1+ba]],
L(b)U(a)P e_7=(q_0+aq_1, bq_0+(1+ba)q_1)^t.           (3)
```

If the second coordinate is nonzero, the same argument applies.  Suppose
it is zero.  The only contribution to the `e_8` coordinate after applying
the native Whitehead `J` is then

```text
x_1(q_0+aq_1).                                        (4)
```

Right multiplication of `(4)` by `q_0` gives

```text
x_1q_0q_0+x_1aq_1q_0=x_1q_0=x_1!=0.                  (5)
```

Thus `(4)` is nonzero, so the image again lies outside
`F_1=<e_2,e_7>_R`.  Every normalizer of `L_0` preserves `F_1`; hence
`J^(-1)R_2R_1P` is not a normalizer in either order.  The Reynolds-support
argument from the one-root proof then gives `(TRN3)`.
