---
rg: 2
id: ordinary-triangle-curl-linear-no-go-proof
kind: route
title: Rotate one supported reflection and use a triangle with one inactive vertex
target: ordinary-triangle-curl-has-linear-inactive-edge
requires:
  - low-odd-square-removes-pairwise-green-stationarity
---

Let `K=XZ`, so `K^*=-K` and `K^2=-I`.  For `j in T\{1}`,

```text
 Q_1(theta)Q_j=cos(2theta)I+sin(2theta)K=exp(2theta K).
```

Hence

```text
 C_(1,j)=exp(4theta K),       C_(j,1)=exp(-4theta K),
 omega_(1,j)=-(sin(4theta)/2)K.                         (OTCP1)
```

If `k notin T`, then `Q_k=I`, so both
`C_(1,k)=Q_1^2=I` and `C_(j,k)=Q_j^2=I`.  This proves
`(OTC4)`.  The two-reflection functional calculus in `(LOS1)--(LOS2)` gives
`R_(1,j)=sin^2(2theta)I` and

```text
 ||omega_(1,j)||_2^2=sin^2(4theta)/4
                    =R_(1,j)(I-R_(1,j)).               (OTCP2)
```

There are exactly `2(m-1)` oriented nonzero edges incident to coordinate
`1`, so

```text
 E_omega=2(m-1)L^(-2)||omega_(1,j)||_2^2.              (OTCP3)
```

Already the `(m-1)(L-m)` ordered triples `(1,j,k)` in `(OTC4)` contribute

```text
 E_curl>=(m-1)(L-m)L^(-3)||omega_(1,j)||_2^2.          (OTCP4)
```

Dividing proves `(OTC6)`.  Letting `theta->0` contradicts `(OTC7)` for
every fixed `C`.
