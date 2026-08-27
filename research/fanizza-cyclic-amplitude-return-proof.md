---
rg: 2
id: fanizza-cyclic-amplitude-return-proof
kind: route
title: Compare the two cyclic traces and insert the heat-filter norm bound
target: fanizza-heat-return-is-one-cyclic-amplitude-product
requires:
  - fanizza-heat-filter-has-uniform-cstar-decay
  - trace-cyclic-rank-mismatch-checksum
---

Since `D_R` is a projection and `p_t(H_m)` is self-adjoint,

```text
B_t^*B_t=p_t(H_m)D_Rp_t(H_m),
tr(B_t^*B_t)=||B_t||_2^2.
```

The Chebyshev heat estimate bounds `||B_t||` by
`sqrt(C_m)/(2t)`, proving `(HAP2)`.  From `(HAP3)`,

```text
|tr(P)-tr(YX)|<=epsilon,
|tr(XY)-tr(A_t)|<=delta.
```

Insert `tr(YX)=tr(XY)` and use positivity of `A_t` to obtain `(HAP4)`.
The HALT statement follows from `p_t(0)=1` and the perfect quotient
`H_m=0`.
