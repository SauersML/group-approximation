---
rg: 2
id: odd-clock-julia-overlap-floor-proof
kind: route
title: Telescope alternating conjugates around the odd clock
target: odd-clock-julia-overlap-floor-is-tracial
requires:
  - julia-dilation-packages-heat-as-one-cross-gram-moment
---

For `S_j=C^(-j)SC^j`, conjugation invariance gives
`||S_(j+1)+S_j||_2=delta`.  Insert alternating signs and telescope to obtain
`(OCJ3)`.  Approximate periodicity bounds `||S_n-S_0||_2` by `2eta`; oddness
therefore gives `2-2eta<=n delta`.

Finally `S_1+S_0=2(Q+E-1)` and

```text
||Q-(1-E)||_2^2
 =tau(Q)+tau(1-E)-2tau(Q(1-E))
 =2tau(QE).
```

This proves the stated floor without using finite-dimensionality.
