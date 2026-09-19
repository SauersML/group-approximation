---
rg: 2
id: positive-toeplitz-square-or-rectangular-proof
kind: route
title: Use trace cyclicity on one reservoir and coordinate inclusion on two reservoirs
target: positive-toeplitz-head-is-square-defect-or-rectangular-escape
requires:
  - toeplitz-head-tail-unital-self-embedding
---

Since normalized trace is cyclic,

```text
tau(XY)=tau(YX).                                         (1)
```

The normalized trace functional has norm one for normalized
Hilbert--Schmidt norm.  Therefore

```text
tau(P)
 =tau(P-(1-XY))+tau(1-YX)
 <=|tau(P-(1-XY))|+|tau(1-YX)|
 <=epsilon_head+epsilon_left.                           (2)
```

Cauchy--Schwarz gives
`(epsilon_head+epsilon_left)^2 <=
2(epsilon_head^2+epsilon_left^2)`, proving `(PTH2)`.

For the escape, the coordinate projection and inclusion in `(PTH3)` obey
`TS=1_E`; their reverse product is the projection onto the `E` summand,
namely `1_F-P_H`.  Both maps have norm one and all displayed relations are
exact.  The trace of `P_H` is `dim(H)/(dim(E)+dim(H))`, which may be any
prescribed positive rational value after choosing dimensions.  This proves
the sharpness and `(PTH5)`.
