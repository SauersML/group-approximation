---
rg: 2
id: quadratic-pair-partial-isometry-proof
kind: route
title: A product of projections is a partial isometry exactly at zero principal angles
target: quadratic-pair-incidence-monomial-entry-forces-commutation
requires: []
---

If `T=pq` is a partial isometry, then

```text
T^*T=qpq
```

is a projection.  Hence

```text
0=qpq-(qpq)^2=q p (1-q) p q
  =((1-q)pq)^*((1-q)pq).
```

Therefore `(1-q)pq=0`, so `pq=qpq`.  Taking adjoints gives
`qp=qpq`, and consequently `pq=qp`.  Conversely, commuting projections
have projection product, which is a partial isometry.  Multiplication by a
nonzero scalar phase does not change the conclusion for a monomial entry.
