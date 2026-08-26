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

For the operator-norm assertion, let
`delta=||YX-1||_op<1`.  The Neumann series gives

```text
||(YX)^(-1)||_op <= 1/(1-delta).
```

Since `X,Y` are endomorphisms of the same finite-dimensional space,
invertibility of `YX` makes both factors invertible, and

```text
X^(-1)=(YX)^(-1)Y,            ||X^(-1)||_op<=1/(1-delta).
```

Using `||X||_op<=1`,

```text
XY-1=X(YX-1)X^(-1),
||XY-1||_op<=delta/(1-delta).
```

If `P` is a nonzero projection then `||P||_op=1`, so the triangle
inequality gives `(PTH2-op)`.  This argument is rank-free and is precisely
where equality of the source and target reservoirs is used.

For the escape, the coordinate projection and inclusion in `(PTH3)` obey
`TS=1_E`; their reverse product is the projection onto the `E` summand,
namely `1_F-P_H`.  Both maps have norm one and all displayed relations are
exact.  The trace of `P_H` is `dim(H)/(dim(E)+dim(H))`, which may be any
prescribed positive rational value after choosing dimensions.  This proves
the sharpness and `(PTH5)`.
