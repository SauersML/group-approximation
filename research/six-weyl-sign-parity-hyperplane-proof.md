---
rg: 2
id: six-weyl-sign-parity-hyperplane-proof
kind: route
title: Average coordinate characters over the odd-parity affine hyperplane
target: six-weyl-sign-proper-moments-miss-top-parity
requires: []
---

Let `K` be the even-parity subgroup of `{+1,-1}^6` and let `Omega_-` be its
odd-parity coset.  The annihilator `K^perp` in the coordinate-character
group has order two and consists of the empty character and the full
six-coordinate character.  Character orthogonality on the coset therefore
gives zero average for every nonempty proper coordinate product, while the
full product is constantly `-1`.

Represent the six coordinate functions as diagonal involutions on
`l^2(Omega_-)`.  Coordinate permutations preserve parity, so the signed
Weyl permutation action is implemented exactly.  The all-negative point has
even parity, hence its joint spectral projection is zero.  Expanding that
projection gives `(SPM6)` and shows that the full parity coefficient is the
unique Fourier coefficient not fixed by the 62 proper moments.  These are
exact finite-dimensional identities, proving the claim.
