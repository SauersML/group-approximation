---
rg: 2
id: complementary-depth-two-a3-a6-proof
kind: route
title: Combine the reverse-product Whitehead identity with two overlapping S3 packets in A6
target: complementary-depth-two-a3-whiteheads-have-a6-gauge-model
requires:
  - reverse-product-whitehead-fold-has-finite-fusion
  - native-weyl-return-gauges-have-s3-model
---

Prefix cancellation gives

```text
(s_i t_(i0))(s_(i0)t_(i1))(s_(i1)t_i)=s_it_i=q_i,
(s_i t_(i0))(s_(i1)t_i)=0,                           (CTAP1)
```

which proves the two A3 and cross-zero tables.  The Steinberg associator
calculation is the same as in the single A3 cell, now with output coefficient
`q_i`.  Root additivity and `q_0+q_1=1` prove `(CTA4)`.

The opposite-root block calculation in
`reverse-product-whitehead-fold-has-finite-fusion` applies at the coordinate
pair `(7,8)` and gives `(CTA6)`.  Restricting that identity to a common
packet chart yields `(CTA8)`.  The native constant-root Weyl factorization
and conjugacy square give `(CTA7)`.

For the finite gauge model, direct permutation multiplication gives

```text
G_0G_1=(1 2)(4 5)=D.
```

Conjugation by `H=(1 3 4)(2 6 5)` sends the edge pairs of `G_0` first to
those of `G_1`, then to those of `D`, and then back to those of `G_0`, proving
`(CTA10)`.  Conjugating `E=(2 3)(5 6)` by `D=(1 2)(4 5)` gives
`F=(1 3)(4 6)`, and conjugating `F` by `E` gives `D`.  Finally direct action
on the six points gives

```text
DE=(1 2 3)(4 5 6),                                   (CTAP2)
```

up to the harmless inverse convention for permutation multiplication.  It
has order three in either convention.  Every displayed permutation is even,
so the entire gauge table lies in the finite group `A_6`.
