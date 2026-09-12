---
rg: 2
id: summable-power-return-detectors-proof
kind: route
title: Evaluate every power moment on the uniform d-cycle spectrum
target: summable-power-return-detectors-miss-growing-cycles
requires: []
---

Let

```text
U_d=diag(1,zeta_d,...,zeta_d^(d-1)).
```

The geometric-series identity gives

```text
tr_d(U_d^k)=d^(-1)sum_(j=0)^(d-1)zeta_d^(jk)
           =1_(d divides k).
```

Substitution yields `(SPR1)`, and the tail of a convergent nonnegative series
tends to zero. For a bounded function `F` with `F(0)=0`, the same calculation
gives `sum_k c_k F(|tr(U_d^k)|)=F(1)sum_m c_(md)`.

For the weighted defect statement, summability of `c_k A(k)` is exactly what
permits summing the individual error bounds without a dimension-dependent
constant. If `A(k)>=1`, it implies summability of `c_k`, so the same cyclic
matrices erase the detector. For a weighted supremum,

```text
sup_k c_k |tr(U_d^k)|=sup_(m>=1)c_(md)<=sup_(k>=d)c_k->0
```

whenever `c_k->0`.
