---
rg: 2
id: adaptive-tensor-amplification-proof
kind: route
title: Use the variance of the padded spectrum and exponential decay of its mean
target: adaptive-tensor-amplification
requires: []
artifacts:
  - research/artifacts/adaptive-tensor-amplification-2026-08-19.md
---

## Direct proof

Choose an eigenvalue `lambda` of `z` with `|lambda-1|>=delta`.  The eigenvalue
multiset of `z'=z directSum 1_d` contains both `lambda` and `1`; let `m` be
its normalized trace.  For any center `c`,

```text
|lambda-c|^2+|1-c|^2 >= |lambda-1|^2/2.
```

Taking `c=m` and using the variance identity for unit-circle eigenvalues gives

```text
1-|m|^2
 = (1/(2d)) sum_j |mu_j-m|^2
 >= delta^2/(4d).
```

Put `x=delta^2/(4d)`.  Since `0<=x<=1`,

```text
|m| <= sqrt(1-x) <= exp(-x/2).
```

For `p=ceil(8d/delta^2)`, `px/2>=1`, so `|m|^p<=e^-1`.  Normalized trace is
multiplicative under tensor products, hence

```text
||(z')^(tensor p)-1||_2^2
 = 2-2 Re(m^p)
 >= 2(1-|m|^p)
 >= 2(1-e^-1).
```

For multiplicativity, tensor telescoping gives
`||A^(tensor p)-B^(tensor p)||<=p||A-B||` for unitaries.  Identity padding
does not change the operator defect, so the amplified defect is at most
`p epsilon`.  The exponent depends only on `d` and `delta`, so it works for
all separated pairs in one finite window simultaneously.
