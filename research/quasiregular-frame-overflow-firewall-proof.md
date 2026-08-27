---
rg: 2
id: quasiregular-frame-overflow-firewall-proof
kind: route
title: Compare fixed-word canonical convergence with the d-squared rank bound
target: quasiregular-frame-dimension-overflow-needs-a-moving-word-window
requires:
  - full-hnn-regularity-is-a-quasiregular-unitary-orbit
  - finite-swap-conjugate-moments-do-not-fold-arithmetic-double
---

`M_d(C)` has Hilbert-space dimension `d^2`, proving the exact orthogonal
rank bound.  An approximate version follows from the Gram matrix: a family
whose Gram matrix is sufficiently close in operator norm to the identity is
linearly independent and still has size at most `d^2`.  Entrywise
convergence for each fixed family gives this only after that family has been
fixed.

For a varying family of size `N_n`, entrywise Gram errors would have to be
`o(1/N_n)` to control the Gram operator norm.  Neither the canonical trace
condition nor vanishing presentation defect provides that uniform rate on
the `N_n^2` moving Britton words.  The exact finite lamp-window models in
`finite-swap-conjugate-moments-do-not-fold-arithmetic-double` calibrate this
failure: every fixed requested window is compatible with finite matrices.
Direct-sum replication further enlarges `d` freely without improving the
controlled window or any normalized error.  This proves the stated
firewall.
