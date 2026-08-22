---
rg: 2
id: s3-standard-operator-fivefold-gauge-proof
kind: route
title: Decompose all nine S3 operator blocks under diagonal conjugation
target: s3-standard-operator-channel-has-fivefold-reduced-gauge
requires: []
---

Use self-duality of `1,epsilon,sigma` and the fusion rules

```text
epsilon epsilon=1,
epsilon sigma=sigma,
sigma sigma=1+epsilon+sigma.
```

Apply them to every ordered pair `(alpha,beta)` in
`V_alpha tensor V_beta^*`.  Listing the nine results gives `(S3O2)` and
counting the occurrences gives multiplicities `3,3,5` for
`1,epsilon,sigma`.  The carrier calculation is independent of every external
`Hom(M_beta,M_alpha)` factor, so amplification cannot reduce the fivefold
standard-channel gauge.

