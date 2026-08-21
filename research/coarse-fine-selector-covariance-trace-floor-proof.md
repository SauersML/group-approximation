---
rg: 2
id: coarse-fine-selector-covariance-trace-floor-proof
kind: route
title: Compare projection traces before decoding the prefix bridge
target: coarse-fine-selector-covariance-has-quarter-trace-floor
requires: []
---

For projections `p,q` in a finite tracial algebra,

```text
||p-q||_2^2
 =tau(p)+tau(q)-2 Re tau(pq).                          (CSP1)
```

Cauchy--Schwarz after compression gives

```text
Re tau(pq)<=min(tau(p),tau(q)).                        (CSP2)
```

Substitution in `(CSP1)` yields

```text
||p-q||_2^2>=tau(p)+tau(q)-2 min(tau(p),tau(q))
             =|tau(p)-tau(q)|.                        (CSP3)
```

Take `p=UeU^*` and `q=f`.  Traciality gives `tau(p)=tau(e)`, so `(CSC1)`
and `(CSP3)` give

```text
||UeU^*-f||_2^2>=tau(P)(1/2-1/4)=tau(P)/4.            (CSP4)
```

Rearranging proves `(CSC5)`.

