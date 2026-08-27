---
rg: 2
id: piecewise-corner-unitary-proof
kind: route
title: Compute the orthogonal initial and range projections of the transport pieces
target: piecewise-group-transport-gives-corner-unitaries
requires: []
---

From `(PGT1)`, `qv_i=v_i=v_iq`, so every piece is in the corner. Also
`v_i^*v_i=p_i` and `v_iv_i^*=r_i`. For `i!=j`, insert the orthogonal range
projections to get `v_i^*v_j=v_i^*r_ir_jv_j=0`; inserting the initial
projections similarly gives `v_iv_j^*=0`. Summing proves `(PGT2)` and the
unitarity of `V`.

Under `(PGT3)`,

```text
v_(s(i))=g_i^(-1)r_i=p_i g_i^(-1)=v_i^*.
```

The summands therefore pair with their adjoints, proving `V=V^*`; together
with unitarity this gives `V^2=q`. Formula `(PGT4)` is the two-cycle special
case.
