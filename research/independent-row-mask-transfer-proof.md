---
rg: 2
id: independent-row-mask-transfer-proof
kind: route
title: Decompose each contraction across its own mask and use G equal to the identity
target: independent-row-masks-transfer-bcs-gap-to-ambient-identity
requires:
  - one-gram-vector-decodes-a-finite-bcs-strategy
---

For every contraction `T` and projection `q`,

```text
||T||_2<=||Tq||_2+||T(1-q)||_2
       <=||Tq||_2+sqrt(tr(1-q)).                       (IRM5)
```

Apply this first to the projection `F_c`, and then to the contraction
`(A_(c,x)-B_x)/2`.  The `G=I` case of
`one-gram-vector-decodes-a-finite-bcs-strategy` gives

```text
Delta<=sum_(c,x)mu_(c,x)
 [||F_c||_2^2+(1/4)||A_(c,x)-B_x||_2^2].              (IRM6)
```

Insert the two instances of `(IRM5)` and collect the repeated predicate
coefficient as `mu_c`.  This is `(IRM2)`.  Under `(IRM3)` only the two
codimension terms remain, giving `(IRM4)`.

