---
rg: 2
id: stw82-support-cover-tracial-capacity-proof
kind: route
title: Charge each covered support to orthogonal label capacity
target: stw82-tracial-capacity-bound-for-support-covers
requires: []
---

For each `v`, traciality and (T2) give

```text
tau(h_v)
 <= sum_(k=1)^d tau(c_(v,k)h_v)+eta.                  (P1)
```

Although `c_(v,k)h_v` need not be positive, its trace equals

```text
tau(c_(v,k)h_v)
 =tau(c_(v,k)^(1/2) h_v c_(v,k)^(1/2)),              (P2)
```

which lies in `[0,tau(c_(v,k))]` because `0<=h_v<=1`.

For fixed `k`, (T1) makes the positive contractions `(c_(v,k))_v`
pairwise orthogonal.  Their sum is a positive contraction, so

```text
sum_v tau(c_(v,k)h_v)
 <=sum_v tau(c_(v,k))
 =tau(sum_v c_(v,k))
 <=1.                                                 (P3)
```

Sum (P1) first over `v`, then use (P3) for each of the `d` labels.  This
gives (T3).  No commutation between a cutter and its support is needed; the
trace cyclically moves one square root in (P2).
