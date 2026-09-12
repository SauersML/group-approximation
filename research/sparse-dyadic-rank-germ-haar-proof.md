---
rg: 2
id: sparse-dyadic-rank-germ-haar-proof
kind: route
title: Use square-root ambient rank and a regular cycle on the sparse corner
target: sparse-dyadic-rank-germ-carries-haar-cyclic-holonomy
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Every `p_n` is nonzero, so the projection sequence has norm one and does not
belong to the norm-direct-sum ideal.  This proves nontriviality of `p`; the
trace calculation gives `(SDH2)`.

For fixed `r`, let `q_(r,n)=0` while `k(n)<r` and otherwise choose it of rank
`2^(k(n)-r)`.  Eventual equality of integer ranks gives `(SDH3)` by the
rank-germ classification.  Since

```text
M 2^(floor(n/2)) <= 2^n
```

eventually for every fixed `M`, the same classification gives
`M[p]<=[1]`.

The trace of the `m`th power of a regular cycle of length `N` is zero unless
`N` divides `m`.  Here `N=2^(k(n))->infinity`, so no fixed nonzero `m` is
divisible by `N` for large `n`.  This proves `(SDH4)` and completes the
claim.
