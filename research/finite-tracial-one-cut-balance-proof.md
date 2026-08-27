---
rg: 2
id: finite-tracial-one-cut-balance-proof
kind: route
title: Compare the two off-diagonal corners by cyclicity of the finite trace
target: finite-tracial-one-cut-balance
requires: []
---

Put `Q=WPW^*`, which is a projection with `tau(Q)=tau(P)`.  Then

```text
||(1-P)WP||_2^2
 = tau(P W^*(1-P) W P)
 = tau(P)-tau(QP),
```

while

```text
||PW(1-P)||_2^2
 = tau(P W(1-P)W^* P)
 = tau(P)-tau(PQ).
```

Traciality gives `tau(QP)=tau(PQ)`, so the squared norms are equal.  Taking
nonnegative square roots proves `(CUT)`.