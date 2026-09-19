---
rg: 2
id: linear-pcpp-hs-tensorization-proof
kind: route
title: Tensor the scalar singular-value inequality with the Hilbert-Schmidt space
target: uniform-linear-pcpp-tensorizes-to-amitsur-hs
requires:
  - quaternion-packet-internalizes-unitary-amitsur-corner
---

Choose an orthonormal basis `(e_alpha)` of `H` and expand every Hilbert-valued
coordinate as `x=sum_alpha x_alpha tensor e_alpha`.  Apply the rooted scalar
inequality `(LPA4)` to every coefficient vector `x_alpha`, square, and sum in
`alpha`.  Parseval gives

```text
||(D_N tensor I_H)x||_C^2
 >=kappa^2||t-N^(-1/2)sum_i v_i||_H^2,
```

with no change in `kappa`.  Equivalently, the scalar positive-semidefinite
inequality `D_N^*D_N>=kappa^2 L_N^*L_N` remains true after tensoring by
`I_H`.  At the finite trigger the leaf sum vanishes, while
`t^*t=P`; the quaternion trace ledger then gives `(LPA8)--(LPA9)`.
