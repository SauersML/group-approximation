---
rg: 2
id: sign-preserving-endomorphism-invariant-trace-proof
kind: route
title: Cesaro-average one marked trace and take a weak-star cluster point
target: sign-preserving-endomorphism-has-invariant-marked-trace
requires: []
---

For `N>=1`, put

```text
tau_N=(1/N) sum_(k=0)^(N-1) tau after alpha^k.                    (SPE2)
```

Every `tau_N` is tracial and `tau_N(J)=-1`.  The tracial state space is
weak-star compact, so a subnet has a cluster point `tau_infinity` with the
same properties.  For every `a in A`,

```text
|(tau_N after alpha)(a)-tau_N(a)|
  = |tau(alpha^N(a))-tau(a)|/N
  <= 2||a||/N.                                                   (SPE3)
```

Passing to the cluster point proves `(SPE1)`.

