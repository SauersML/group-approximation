---
rg: 2
id: amplified-sheaf-criterion-gives-collective-cofilling
kind: route
title: Apply the degree-zero sheaf criterion uniformly to all finite direct sums
target: collective-sheaf-cofilling-for-good-ltc
requires:
  - inner-tensor-agreement-is-amplification-stable
---

Fix a finite family of cochains `f_1,...,f_T in C^0(X,F)`.  Form the direct-
sum sheaf

```text
F^[T](x)=F(x)^T
```

with componentwise restriction maps, and the single amplified cochain
`f=(f_1,...,f_T)`.  Its block-support Hamming norm is exactly the union norm:

```text
||f||_block=|union_t supp(f_t)|,
||d f||_block=|union_t supp(d f_t)|.                     (ASC1)
```

Audit the hypotheses of First--Kaufman Theorem 8.10 for the double-Cayley
sheaf.

* The poset, weights, upper graphs, and no-intersection graph do not depend
  on the sheaf, so conditions (2a)--(2c), and all constants `F,L`, are
  unchanged by amplification.
* Conditions (1a) and (1b) are degree-minus-one coboundary expansion of
  restriction maps realizing the inner codes.  If an amplified stalk vector
  is nonzero, one scalar component is a nonzero inner-code word.  The union
  of its nonzero restrictions therefore has at least the original relative
  distance.  These two local constants are unchanged.
* Condition (1c) is `cbe_0` on the complete-bipartite row-column link.
  Lemma 9.4 identifies its one-summand version with tensor-code agreement
  testability.  For `F^[T]` it is exactly
  `inner-tensor-agreement-is-amplification-stable`, so the same positive
  lower bound is available uniformly in `T`.

Theorem 8.10 therefore gives one constant `s>0`, independent of `T`, with

```text
||d f||_block >= s dist_block(f,Z^0(X,F^[T])).           (ASC2)
```

Choose `z=(z_1,...,z_T)` realizing the distance.  Since the differential is
componentwise, `z_t in Z^0(X,F)` for every `t`.  Put `a_t=f_t-z_t`.  Then

```text
d a_t=d f_t,
|union_t supp(a_t)| <= s^(-1)|union_t supp(d f_t)|.      (ASC3)
```

This is collective cofilling.  The First--Kaufman stalk dimensions and
local degrees are fixed along the family, so expanding every stalk block
into binary coordinates compares block support with ordinary binary support
by fixed constants.  Thus `(ASC3)` gives `(SCC1)` for a bounded-degree
binary parity presentation, and
`collective-cofilling-is-common-erasure-cleaning` converts it to the desired
erasure-cleaning statement.
