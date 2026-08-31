---
rg: 2
id: right-core-cayley-average-relative-toeplitz-proof
kind: route
title: Average a right-core-equivariant gauge into a complete relative Toeplitz kernel
target: right-core-cayley-average-gives-toeplitz-window
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
---

Extend a coset gauge by `W_(tb)=Z_t beta(b)` and set

```text
F(k)=|G|^(-1) sum_(g in G) W_g^* W_(gk).
```

The matrix `[F(g_i^(-1)g_j)]` is an average of Gram matrices and is
positive. Right-core equivariance gives `F(b)=beta(b)). Cauchy--Schwarz
applied to
`F(s)-U_s=|G|^(-1)sum_g W_g^*(W_(gs)-W_gU_s)` gives the square-root
Cayley-energy estimate. The finite relative corner follows from the
positive-definite-window claim.
