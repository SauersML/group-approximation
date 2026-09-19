---
rg: 2
id: direct-product-malnormality-proof
kind: route
title: Centralizers force both direct factors into a malnormal subgroup
target: two-player-product-has-no-proper-nontrivial-malnormal-subgroup
requires: []
---

Let `G=A x B`, where `A` and `B` are nontrivial, and let `K<=G` be a
nontrivial malnormal subgroup.  Malnormality first gives the elementary
centralizer containment

```text
k in K\{1}  ==>  C_G(k) <= K.                              (DPM2)
```

Indeed, if `g` centralizes `k`, then
`k in K intersect gKg^(-1)`; because `k!=1`, malnormality forces `g in K`.

Choose `1!=(a,b) in K`.  If `a!=1`, then `(a,1)` centralizes `(a,b)`, so
`(a,1) in K` by `(DPM2)`.  Every element of `{1} x B` centralizes the
nonidentity element `(a,1)` of `K`, and hence

```text
{1} x B <= K.                                               (DPM3)
```

Choose `b_0!=1` in `B`.  Now `(1,b_0) in K`, while every element of
`A x {1}` centralizes `(1,b_0)`.  A second application of `(DPM2)` gives
`A x {1} <= K`.  Thus `K=G`.

If instead `a=1`, then `b!=1`; exchanging `A` and `B` in the preceding
argument again gives `K=G`.  Therefore a malnormal subgroup of a direct
product of two nontrivial groups is either trivial or the whole product.
