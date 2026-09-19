---
rg: 2
id: kt-ab-marked-return-cylinder-proof
kind: route
title: Conjugate one polynomial root to the Kun--Thom Laurent mark
target: kt-ab-marked-return-is-the-first-mixed-cylinder
requires:
  - kt-two-positive-compressors-generate-full-obstruction
  - kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath
  - two-point-approximation-fails
  - two-site-a5-plancherel-center-separates-mark
  - two-site-a5-center-has-exact-boundary-countermodel
---

The displayed lower-triangular matrix `L` has determinant one and first
column `-(1,1,1)`.  Since `<A,B>=SL_3(Z)`, it is an `A,B` word.  Monomial
substitution sends `x_1` to `(x_1x_2x_3)^(-1)`, proving the conjugacy formula
for `h`.  The external orbit has trivial elementary component, so `hGamma`
is outside it.  The established marked-pair failure and A5 center calculation
then show that this two-site PVM is terminal once a coherent actor table is
available, while the exact fixed-pair boundary countermodel shows that its
separate covariance does not manufacture such a table.
