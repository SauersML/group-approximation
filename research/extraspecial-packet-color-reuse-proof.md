---
rg: 2
id: extraspecial-packet-color-reuse-proof
kind: route
title: Put all packets of one proper vertex color on one tensor factor
target: bounded-degree-extraspecial-packets-have-fixed-reuse-model
requires: []
---

Choose a proper coloring

```text
c:V(Lambda)->{0,...,Delta}.
```

On `H=(C^d_K)^(tensor (Delta+1))`, map `K_v` through the fixed marked
representation on tensor factor `c(v)` and trivially on the other factors.
If `uv` is an edge, `c(u)!=c(v)`, so the two images commute elementwise.

In every tensor factor the central involution acts as `-I` on that factor
and identity elsewhere, which is the same scalar `-I_H`; hence the identified
central marks are respected.  All packet and edge relations hold exactly,
giving `(BEP1)`.

