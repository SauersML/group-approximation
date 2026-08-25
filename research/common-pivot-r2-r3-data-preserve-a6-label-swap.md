---
rg: 2
id: common-pivot-r2-r3-data-preserve-a6-label-swap
kind: claim
title: Common-pivot R2 and R3 data still preserve the A6 label-swap gauge
invalidates:
  - common-pivot-r2-or-r3-anchor-closes-a6-seam
distinct_from:
  bare-r5-a6-collision-does-not-synchronize-shared-labels: that uses only the two Carmichael charts and their nonshared R5 pair; this extends the countermodel by exact R2 transport arms and by exact binary split refinements.
  shared-endpoint-r2-r3-anchor-has-linear-seam-bound: that positive theorem assumes a label arm is transported to the same output in both contexts, or that the same coarse parent and complementary child are retained; the models here share only the pivot and permute every label-sensitive arm.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that is an unbounded private-gauge construction; these are finite permutation models on six and twelve points at one A6 seam.
---

The exact label-swap countermodel survives the two natural enrichments which
retain only a common pivot.

For the R2 enrichment, on

```text
Omega={1,2,3,4,p,q}
```

put

```text
r=(p q),       s_i=(i p),       t_i=(i q),
c_i=(i p q)=t_i s_i.                                             (CPA1)
```

Then every label arm satisfies the exact R2-shaped transport identity

```text
s_i^r=t_i.                                                       (CPA2)
```

Use the two contextual charts

```text
X=(c_1,c_2,c_3),             Y=(c_2,c_1,c_4),                    (CPA3)
```

and swap the corresponding pairs `(s_1,t_1)` and `(s_2,t_2)` in the second
chart.  Both charts share the literal pivot `r`; all their transport
identities `(CPA2)`, local Carmichael relations, and the nonshared R5
collision hold exactly.  Nevertheless, on the five-dimensional standard
summand of the permutation representation,

```text
||X_1-Y_1||_2^2=||X_2-Y_2||_2^2=6/5.                            (CPA4)
```

For the R3 enrichment, replace every letter `x in Omega` by two children
`x0,x1`.  Lift a permutation diagonally to both child layers.  In particular

```text
hat(c_i)=(i0 p0 q0)(i1 p1 q1),
hat((x y))=(x0 y0)(x1 y1).                                      (CPA5)
```

Every lifted transposition has the exact split

```text
hat((x y))=(x0 y0)(x1 y1),                                     (CPA6)
```

with commuting involutory children.  The doubled versions of `(CPA3)` share
the literal split pivot `hat(r)` and may even retain all contextual arm
splits, but swapping labels `1,2` together with all their children preserves
every such identity.  On the eleven-dimensional standard summand of the
twelve-point permutation representation,

```text
||hat(c_1)-hat(c_2)||_2^2=12/11.                                (CPA7)
```

Hence a common-pivot R2 cell, a common-pivot R3 split, or even all
within-chart copies of those identities do not yield pointwise seam control.
The anchor must retain a label-sensitive endpoint *across* the two contexts;
merely enriching both contexts equivariantly leaves the gauge intact.

