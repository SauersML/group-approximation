---
rg: 2
id: unstabilized-reset-pencil-symmetry-audit-proof
kind: route
title: Compare the primary similarity signatures of T, its inverse, and I plus T
target: unstabilized-reset-pencils-have-no-s3-symmetry
requires:
  - fanizza-schur-menu-has-common-codimension-one-residual
---

For an invertible pair `(B_1,B_2)`, simultaneous left/right equivalence sends
`B_1^(-1)B_2` to a similar matrix.  Swapping the two pencil directions sends
it to `T^(-1)`; fixing the first and adding it to the second sends it to
`I+T`.  The replay computes the rational-primary similarity signature of all
three matrices exactly over `F_2`.  A mismatch is a certificate that the
corresponding pencil generator has no strict equivalence.  Every compatible
plane fails both generator tests.
