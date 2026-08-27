---
rg: 2
id: common-range-isometries-have-maximal-gram-overlap-proof
kind: route
title: Expand the cross-Gram square through the common final projection
target: common-range-isometries-have-maximal-gram-overlap
requires: []
---

Using the tracial `L^2` norm and the common final projection,

```text
||S^* T||_2^2
 = tau((S^*T)^*(S^*T))
 = tau(T^* S S^* T)
 = tau(T^* E T).
```

Since `T T^*=E`, one has `E T=(T T^*)T=T`, so the last expression is

```text
tau(T^*T)=tau(TT^*)=tau(E).
```

No comparison of the initial projections is used.  In particular the overlap
cannot tend to zero while `tau(E)` stays bounded below.