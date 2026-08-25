---
rg: 2
id: root-relative-transport-cross-gram-proof
kind: route
title: Rewrite transport Gram energy as marked-root carrier overlap
target: root-valued-relative-transport-forces-cross-gram
requires:
  - binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
---

Write `G_i=rho(g_i)` and `Q_i=G_iPG_i^*`.  Since `S_i=G_iP` is an isometry
on `PH`, traciality gives

```text
tau(S_1^*S_2S_2^*S_1)
 =tau(Q_1Q_2)
 =tau(P rho(u) P rho(u)^*).                            (RTP1)
```

Under `(RTG2)`, the second projection in the last overlap is the nontrivial
spectral carrier of the marked-index-disjoint nonzero root `x_ij(a)`.  It is
conjugate to `P`, so it has exactly the same trace.  The direct
marked-carrier estimate `(URR5)`
from `binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale` therefore
gives

```text
tau(P rho(u)P rho(u)^*) >= tau(P)/16,                  (RTP2)
```

which proves `(RTG3)`.  Fixed-word telescoping, the robust direct-overlap
estimate, and cyclicity of normalized trace give the asymptotic version.
