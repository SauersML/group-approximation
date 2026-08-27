---
rg: 2
id: partial-isometry-gram-is-range-overlap-proof
kind: route
title: Cycle the trace from cross-Gram to the two final projections
target: partial-isometry-gram-is-range-overlap
requires: []
---

By definition of the tracial `L^2` norm,

```text
||S^*T||_2^2
 = tau((S^*T)^*(S^*T))
 = tau(T^* S S^* T)
 = tau(T^* F T).
```

Traciality moves the outer `T^*,T` together:

```text
tau(T^* F T)=tau(F T T^*)=tau(FG).
```

For projections `F,G`,

```text
||FG||_2^2
 = tau((FG)^*(FG))
 = tau(G F G)
 = tau(F G^2)
 = tau(FG).
```

Hence all three quantities are equal.  The formula does not require `F` and
`G` to commute.