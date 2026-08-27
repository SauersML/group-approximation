---
rg: 2
id: onehot-predicated-direct-sum-decoder-proof
kind: route
title: Orthogonal branch sectors make predicated copies a controlled strategy
target: onehot-predicated-direct-sum-decoder
requires: []
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
---

Orthogonality and commutation give

```text
U_i^*=U_i,
U_i^2=sum_a Q_a G_(a,i)^2=Q,
```

so `U_i` is an involution in the unital corner `QMQ`.  For every branch `a`,

```text
Q_a U_i = Q_a G_(a,i).
```

Therefore, for a branch equation whose participating copies commute,

```text
Q_a product_(i in I) U_i
 =Q_a product_(i in I) G_(a,i)
 =Q_a H_(a,I).
```

Since `Q_a Z_a=-Q_a`, one has
`Q_a Z_a^b=(-1)^b Q_a`, and hence

```text
Q_a(product U_i-(-1)^b)
 =Q_a(H_(a,I)-Z_a^b).
```

Left multiplication by a projection is `L^2`-contractive, proving (DS1).
Square, sum over orthogonal branch sectors and over the finite check weights,
and divide by `q=tau(Q)` to pass from `tau` to the normalized corner trace.
This is (DS2).
