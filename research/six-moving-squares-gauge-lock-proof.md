---
rg: 2
id: six-moving-squares-gauge-lock-proof
kind: route
title: Cancel the label part of each moving square and telescope the reservoir differences
target: six-ungauged-moving-squares-lock-seven-gauges
requires: []
---

Replace the four factors in `(SGL3)` successively by their ideal forms from
`(SGL1)--(SGL2)`.  All factors are contractions, so the replacement costs
at most

```text
eta_(k+1)+zeta_k+zeta_(k+1)+eta_k.                   (1)
```

By `(SGL4)`, the resulting ideal difference is

```text
M_(k+1)N_k tensor (D_(k+1)-D_k).                     (2)
```

The label factor is unitary, hence its normalized Hilbert--Schmidt norm is
exactly the reservoir norm.  The triangle inequality proves `(SGL5)`.

Summing `(SGL5)` along the path from `0` to `k` bounds
`||D_k-D_0||_2`.  Replacing the factors of `D_6...D_0` one at a time by
`D_0` and using unitary invariance gives

```text
||D_0^7-1||_2
 <=rho+sum_(k=1)^6||D_k-D_0||_2.                     (3)
```

Since `D_0^2=1`, `D_0^7=D_0`, proving `(SGL7)`.  Finally, if the comparison
graph is disconnected, assign `D=1` on one component and one fixed
nontrivial involution on another; every retained edge equality remains
exact.  This proves the stated sharpness.
