---
rg: 2
id: stw27-real-rank-zero-almost-divisibility
kind: claim
title: Simple non-type-I real-rank-zero algebras have almost divisible Cuntz semigroups
distinct_from:
  thiel-stable-rank-one-ranks-close-purity-with-comparison: that theorem obtains divisibility from stable-rank-one rank realization; this theorem uses large finite-dimensional subalgebras in projection corners and does not assume stable rank one.
  stw27-coordinate-euler-slack-obstructs-compact-dividers: that no-go theorem concerns particular coordinate-heavy homogeneous blocks; this theorem proves that every compact class in a simple non-type-I real-rank-zero algebra has dividers after passing to the ambient algebra.
artifacts:
  - research/artifacts/stw27-real-rank-zero-divisibility-audit-2026-08-30.md
---

Let `A` be a separable simple non-type-I C-star algebra of real rank zero.
Then `Cu(A)` is almost divisible: for every `x',x in Cu(A)` with `x'<<x`
and every integer `n>=1`, there is `y in Cu(A)` such that

```text
n y <= x,             x' <= (n+1)y.
```

Consequently, if `A` also has strict comparison, then `A` is pure.  In
particular, part (1) of STW Problem XXVII has a positive answer for all
unital simple separable nuclear non-elementary real-rank-zero algebras.

Neither nuclearity nor stable rank one is used to obtain almost
divisibility.
