---
rg: 2
id: primitive-character-finitary-support-proof
kind: route
title: Count primitive dual vectors at each divisor and preserve finitary determinants under conjugation
target: finite-modulus-finitary-kernels-have-uniform-support-rank
requires: []
artifacts:
  - research/artifacts/composite-jacobson-uniform-rank-and-normality-2026-09-08.md
---

The artifact proves all assertions. The row and column root groups
generate E_N(Z/q). Levi orbits on their duals are classified by a
divisor d|q. For effective modulus k=q/d>1 and r=N-1, the fraction
of primitive vectors whose first coordinate is zero equals

    (1/k) product_(p|k)(1-p^(-(r-1)))/(1-p^(-r))<1/2.

Thus each root subgroup's active dimension is at most twice the
head moving rank. Intersecting their fixed spaces gives four.
The shift representation identifies the defect matrix units and
embeds all finitary elementary transvections. Conjugation preserves
the finitary ideal, and Sylvester's finite rectangular determinant
identity preserves determinant one. Over Z/q, SL_fin=E_fin, proving
normality.
