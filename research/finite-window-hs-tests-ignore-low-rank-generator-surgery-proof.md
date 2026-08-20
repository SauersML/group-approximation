---
rg: 2
id: finite-window-hs-tests-ignore-low-rank-generator-surgery-proof
kind: route
title: Telescope unitary words and charge only relative perturbation rank
target: finite-window-hs-tests-ignore-low-rank-generator-surgery
requires: []
---

For a matrix `T` of rank at most `r`, its nonzero singular values are at most
`||T||_op`, hence

```text
||T||_2^2 <= (r/d)||T||_op^2.
```

For unitaries `U,V`, `||U-V||_op<=2`; therefore
`rank(V-U)<=r` gives `||V-U||_2<=2 sqrt(r/d)`.  Inversion preserves the
normalized Hilbert--Schmidt distance because

```text
V^(-1)-U^(-1)=V^(-1)(U-V)U^(-1).
```

Finally telescope a word one letter at a time.  If `X_i,Y_i` are unitary,
bi-invariance and the triangle inequality give

```text
||X_1...X_L-Y_1...Y_L||_2
 <= sum_i ||X_i-Y_i||_2.
```

Apply this with `X_i=V_(a_i)^(eps_i)` and
`Y_i=U_(a_i)^(eps_i)`.  This proves the displayed estimate.  A fixed finite
multiplication table is encoded by finitely many fixed words, so if every
relative rank tends to zero, the maximum of all its defects tends to zero as
well.
