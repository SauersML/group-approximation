---
rg: 2
id: s3-weighted-two-generator-covariance-controls-commutant-distance
kind: claim
title: The weighted two-involution S3 covariance form has an exact spectral exchange rate
distinct_from:
  s3-two-generator-covariance-controls-commutant-distance: that is the symmetric p=q=1 specialization; this claim exposes the full one-parameter tradeoff between the two named covariance directions.
---

Let `rho:S_3->U(d)` be any finite-dimensional unitary representation, let
`s,t` be involutions generating `S_3`, and put

```text
a=||U rho(s)-rho(s)U||_2,
b=||U rho(t)-rho(t)U||_2
```

for a unitary `U`.  For every `p,q>0`, define

```text
lambda(p,q)=p+q-sqrt(p^2-pq+q^2).
```

If `C_K` is the unitary group of `rho(S_3)'`, then

```text
lambda(p,q) dist_2(U,C_K)^2 <= p a^2+q b^2.           (S3-WCOV)
```

The constant is independent of dimension and multiplicities.  It is homogeneous
in `(p,q)`, and `lambda(1,1)=1`, recovering the established symmetric theorem.

This weighted form lets an atlas contradiction price the synthesized `t21`
direction and the directly observed `t12` direction differently rather than
forcing an artificial one-to-one exchange rate.