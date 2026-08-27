---
rg: 2
id: kt-double-amalgam-twist-proof
kind: route
title: Build canonical Kun--Thom vertex marginals with a large exact amalgam twist
target: kt-double-canonical-vertex-marginals-admit-large-amalgam-twists
requires:
  - kun-thom-nonsofic-wreath
  - kt-pair-group-double-is-nonsofic
---

The projection from the Theorem E semidirect product onto `SL_d(Z)` kills
`Gamma`.  Residual finiteness of `SL_d(Z)` supplies `(KDT4)`, and taking the
product with any residual sequence for `G` supplies `(KDT5)` while preserving
pointwise convergence of the finite regular characters.

For `l in L_n`, left multiplication preserves every left coset `L_n x`, so
the diagonal sign `U_n` commutes with `lambda(l)`.  If
`L_n x=L_n k_n^(-1)x`, cancellation on the right gives `k_n^(-1) in L_n`,
contrary to `(KDT5)`.  Hence the two signs compared at each `x` in `(KDT7)`
are distinct independent Rademacher variables, whose squared difference has
expectation `2`.  Averaging over `x` proves `(KDT7)` and gives one deterministic
choice with energy at least `2`.

Unitary invariance of normalized Hilbert--Schmidt norm turns `(KDT7)` into
`(KDT3)`.  Commutation with `lambda(L_n)` proves exact amalgam agreement, so
the universal property of `G *_Gamma G` gives the claimed exact
representations.  Finally the two vertex characters agree with the finite
regular character of `q_n(G)` and converge to `delta_e` by residuality.

