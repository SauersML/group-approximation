---
rg: 2
id: stw82-tracial-unit-coupling-obstruction-proof
kind: route
title: Double-count a full coupled partition with a trace
target: stw82-traces-block-unit-coupled-colour-reduction
requires: []
---

Let `tau` be a tracial state of `B`.  For fixed `k`, the positive
contractions `(c_(v,k))_(v in V)` are pairwise orthogonal.  Their sum is
therefore again a positive contraction, and hence

```text
sum_(v in V) tau(c_(v,k))
 =tau(sum_(v in V) c_(v,k))
 <=tau(1_B)=1.
```

On the other hand, taking the trace of the partition identity for every
`v` and then summing gives

```text
|V|
 =sum_(v in V) sum_(k=1)^d tau(c_(v,k))
 =sum_(k=1)^d sum_(v in V) tau(c_(v,k))
 <=d.
```

Thus fewer than `|V|` labels are impossible.  Notice that no commutation is
required between pieces having different labels; linearity of the trace is
exactly what makes the count insensitive to that issue.
