---
rg: 2
id: binary-toeplitz-bernoulli-haar-fixed-point-proof
kind: route
title: Read the binary defect roots in the faithful regular trace
target: binary-toeplitz-root-refinement-has-a-bernoulli-haar-fixed-point
requires:
  - binary-schur-child-toeplitz-self-embedding
---

Put `e_j=x^jPy^j`.  The Toeplitz normal form makes the `e_j` linearly
independent orthogonal idempotents, so injectivity and additivity of
`a |->x_12(a)` identify the generated root subgroup with
`direct_sum_N C_p`.  Its canonical group trace is the iid Haar trace.
Finally `(BST8)` and HNN covariance give
`t^n x_12(P)t^-n=product_(j<2^n)x_12(e_j)`.  Fourier transforming the
resulting equation `mu=mu star mu` on `C_p` leaves exactly the identity and
Haar solutions, and the regular trace realizes Haar.
