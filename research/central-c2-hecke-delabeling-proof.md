---
rg: 2
id: central-c2-hecke-delabeling-proof
kind: route
title: Cancel the paired central labels both inside and outside the Hecke corner
target: central-c2-hecke-mask-has-an-ambient-delabeling-word
requires: []
---

Centrality gives `px_i=x_ip` and `pk=p`.  Hence

```text
p lambda(x_i k)p=p lambda(x_i)p,
```

and this is a unitary in the corner `pL(H)p`.  Cancelling it proves `(CHM2)`.
In the ambient label group,

```text
x_i (x_i k)^(-1) k^(-1)
 =x_i k^(-1)x_i^(-1)k^(-1)=1,
```

where `k^2=1` and centrality are used.  This proves `(CHM3)` and the trace
claim.

