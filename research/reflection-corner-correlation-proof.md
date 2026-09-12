---
rg: 2
id: reflection-corner-correlation-proof
kind: route
title: Multiply the two-by-two reflection blocks and take normalized trace
target: reflection-corner-encoding-exposes-real-payload-correlations
requires: []
---

Direct multiplication gives `r_u^*=r_u`, `r_u^2=1`, and

```text
r_u r_1=diag(u,u^*),
```

which proves `(RCE2)`.  Likewise

```text
r_u r_v=diag(uv^*,u^*v).
```

Traciality gives `tau(u^*v)=overline(tau(uv^*))`, proving `(RCE3)` after
averaging the two diagonal blocks.  A product of an odd number of off-diagonal
matrices remains off-diagonal, so its matrix trace is zero.

