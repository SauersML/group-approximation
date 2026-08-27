---
rg: 2
id: finite-tag-eight-slice-no-compression-proof
kind: route
title: Apply Schur orthogonality to the three branch intertwiners
target: finite-tag-covariance-cannot-compress-eight-slice-orbit
requires:
  - eight-slice-bookkeeping-symmetrizes-s3-failures
---

For `i!=j`, covariance gives

```text
pi_i(h) T_i^*T_j = T_i^* rho(h)T_j = T_i^*T_j pi_j(h).
```

Pairwise disjointness and Schur orthogonality imply `T_i^*T_j=0`.  Since
every `T_i` is an isometry, the range dimensions add inside `K`, proving
`(FTC2)`.  Substitute the trace counts `(ESB4)` to obtain `(FTC3)` and compare
with the parent trace.  The normalized-trace version is unchanged under any
fixed matrix amplification.
