---
rg: 2
id: codense-coset-outlier-proof
kind: route
title: Kazhdan-project the one-hot base-coset labels
target: codense-kazhdan-coset-action-forces-permutation-outliers
requires: []
---

From an orbit atlas of error `epsilon`, label each good vertex by the one-hot
vector attached to its named base coset.  Every Kazhdan generator changes the
label on at most `2epsilon` of the vertices, so its squared displacement is at
most `4epsilon`.  Kazhdan projection places the label vector within
`2 sqrt(epsilon)/kappa` of the `C`-fixed space.  Co-density in the finite
permutation image identifies that space with the `A`-fixed space, whence the
chosen `h in A\C` changes the label on a fraction at most
`8epsilon/kappa^2`.

Atlas covariance and injectivity say that `h` changes the base-coset label
whenever both endpoints are good, a fraction at least `1-2epsilon`.  Thus
`1-2epsilon<=8epsilon/kappa^2`, which is the stated gap.
