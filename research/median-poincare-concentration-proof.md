---
rg: 2
id: median-poincare-concentration-proof
kind: route
title: Pin the mean with the median after applying the Poincare gap
target: median-poincare-concentration
requires: []
---

Put `m = tau_q(f)` and

```text
sigma = ||f - m q||_(2,q),
E = sum_(s in S) ||a_s f - f a_s||_(2,q)^2.
```

The assumed gap applied directly to `x=f` gives

```text
sigma <= E^(1/2)/kappa.
```

It remains only to compare the mean `m` with the median `1/2`.  If
`m >= 1/2`, the spectral set `{f <= 1/2}` has `tau_q`-mass at least `1/2`.
On that set `|f-m| >= m-1/2`, hence

```text
sigma^2 = tau_q((f-mq)^2) >= (1/2)(m-1/2)^2.
```

Thus `m-1/2 <= sqrt(2) sigma`.  If `m <= 1/2`, use instead the spectral set
`{f >= 1/2}`, which also has mass at least `1/2`, and obtain
`1/2-m <= sqrt(2) sigma`.  Therefore in all cases

```text
|m-1/2| <= sqrt(2) sigma.
```

The triangle inequality now gives

```text
||f-(1/2)q||_(2,q)
 <= ||f-mq||_(2,q) + |m-1/2|
 <= (1+sqrt(2)) sigma
 <= ((1+sqrt(2))/kappa) E^(1/2).
```

Finally normalized Cauchy--Schwarz gives the same bound in `L^1`.  Nothing in
the proof uses `a_s^* a_s=q`, trace preservation by `a_s`, or even normality
of the `a_s`; only the displayed Poincare inequality is used.