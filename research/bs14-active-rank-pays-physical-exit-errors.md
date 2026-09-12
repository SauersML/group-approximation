---
rg: 2
id: bs14-active-rank-pays-physical-exit-errors
kind: route
title: Charge arbitrary physical exit mismatch to the thresholded active source rank
target: bs14-polar-exits-retain-the-common-physical-reflection
requires: []
---

For a high singular subspace of `D_i` above `theta`, Markov's inequality
gives

```text
theta^2 rank(high_i)<=||D_i||_F^2.
```

The aligned common source has dimension no larger than the sum of the two
high-carrier ranks.  Since the two cubic energies are part of `ed` and
`theta=c e^(1/4)`, this proves `(PER3)`.

Each `F_i,H_i:E->H` is a contraction and `X` is unitary.  Therefore

```text
||XF_i-H_i||_F^2
 <=2||XF_i||_F^2+2||H_i||_F^2
 <=4 dim(E).
```

Sum over the two rows and use `(PER3)`.  This proves `(PER4)` and hence
`(PER2)`.  No covariance of singular vectors with `X` is needed: arbitrary
loss of the physical exit equation is already supported on `o(d)` active
rank.
