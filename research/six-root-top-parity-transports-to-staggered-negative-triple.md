---
rg: 2
id: six-root-top-parity-transports-to-staggered-negative-triple
kind: claim
title: The six-root top parity transports to one staggered negative-root triple
distinct_from:
  half-period-sector-sits-inside-two-level-exit: that bounds the wrong sign for one transverse half-period transport by a two-level conductor exit; this computes the exact image of the unique six-way parity statistic needed to authenticate the common carrier.
  exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss: that bounds common representation multiplicity across one parahoric shift; this is a literal congruence identity before any representation decomposition.
  six-weyl-sign-proper-moments-miss-top-parity: that proves the source parity statistic is necessary; this identifies its exact denominator image once it is supplied.
---

**ESTABLISHED EXACT TRANSPORT IDENTITY.**  Put

```text
Lambda=SL_3(Z),
h=diag(2,1,1/2),
Gamma_a=ker(Lambda -> SL_3(Z/2^a Z)).
```

For `a>=4`, let

```text
r_a=product_(i!=j) x_ij(2^(a-1)),                       (SPT1)
```

where the order is immaterial modulo `Gamma_a`.  Then `r_a` belongs to the
domain of the parahoric conjugation by `h`, and in `Lambda/Gamma_a`

```text
h r_a h^-1
 =x_21(2^(a-2)) x_32(2^(a-2)) x_31(2^(a-3)).           (SPT2)
```

The three displayed factors commute modulo `Gamma_a` and have orders
`4,4,8`, respectively.

Indeed

```text
h x_ij(t) h^-1=x_ij((d_i/d_j)t),
(d_1,d_2,d_3)=(2,1,1/2).                               (SPT3)
```

Thus the `12,23,13` top-layer factors acquire parameters
`2^a,2^a,2^(a+1)` and vanish modulo `Gamma_a`, whereas the `21,32,31`
factors acquire parameters `2^(a-2),2^(a-2),2^(a-3)`.  The only possible
extra commutator is an `x_31` term whose parameter is divisible by
`2^(2a-4)`, hence by `2^a` for `a>=4`.  This proves `(SPT2)`.

Consequently the full six-sign moment isolated by
`six-weyl-sign-proper-moments-miss-top-parity` has a precise denominator
target: it is a three-root moment spread across the last three dyadic
layers, not another top-layer parity moment.  This removes ambiguity about
the algebraic endpoint of the rectangular transition.

It does **not** provide the needed arbitrary-microstate estimate.  Written
in a fixed finite presentation, both sides use powers growing like `2^a`,
so naive relator telescoping has depth-dependent loss.  The remaining
analytic gate is exactly a dimension-free way to carry the source parity
coefficient to the staggered triple, or else charge the intervening
conductor exit.
