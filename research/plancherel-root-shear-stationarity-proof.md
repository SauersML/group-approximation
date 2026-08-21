---
rg: 2
id: plancherel-root-shear-stationarity-proof
kind: route
title: Average permutation matrices and retain the uniform vector
target: plancherel-root-shears-have-no-compression-pressure
requires:
  - steinberg-root-shear-plancherel-covariance
---

Every automorphism of `H` induces a bijection of `dual(H)`, so its matrix
`P_(alpha_j^*)` has exactly one `1` in every row and every column.  Their
convex combination `(PRN1)` is therefore doubly stochastic.  Multiplication
by the uniform vector gives `(PRN2)` entry by entry.  The total mass of any
transported vector is also preserved because the all-ones row vector is
fixed on the left.

Thus a strict loss requires information not present in the permutation
matrices: disjointness of several ranges, a capacity restriction, or a
boundary which leaves the chosen finite window.  This is exactly the stated
fence.
