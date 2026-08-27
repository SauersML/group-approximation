---
rg: 2
id: qutrit-diamond-synchronizer-proof
kind: route
title: Subtract the two Culf--Mastel triangle residual identities
target: qutrit-diamond-robustly-synchronizes-pvms
requires: []
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
---

Culf--Mastel Lemma 8.3 gives

```text
sum_c ||P_c(x)+P_c(a)+P_c(b)-1||_2^2=2D(x,a,b),
```

and the identical formula with `x` replaced by `y`.  For each colour,
`P_c(x)-P_c(y)` is the difference of the two displayed residuals.  The
squared triangle inequality gives twice the sum of their squared norms.
Summing over colours proves `(QDS2)`.

