---
rg: 2
id: marked-hyperoctahedral-table-breaker-proof
kind: route
title: Exactify the whole signed-permutation table and use its minimum odd degree
target: marked-hyperoctahedral-table-linear-dimension-breaker
requires:
  - low-dimensional-hyperoctahedral-packet-groupifies-any-predicate
  - marked-clifford-table-exponential-dimension
---

Use only the all-pairs Gowers--Hatami theorem quoted in the proof of the
marked Clifford table result.  It gives an exact representation `rho` of
`W_m` on dimension

```text
d<=d'<=d/(1-4epsilon^2)                                 (1)
```

whose compression differs from `f(J)` by at most `42epsilon`.  Equation
`(MHB1)` forces the exact `J=-1` subspace to be nonzero.  Every marked
irreducible of `W_m` has dimension at least `m` by the bipartition formula,
so `d'>=m`.  Combine this with `(1)` to obtain `(MHB2)`.

Under `(MHB3)`, every marked irreducible in `rho` lies in the low-dimensional
classification `(HLP3)`, so its selector joint spectrum is the encoded
allowed set.  Finally `(MHB4)` contradicts `(MHB2)` in the reported
dimension.
