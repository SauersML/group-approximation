---
rg: 2
id: rohlin-cut-and-diagonal-polynomial-proof
kind: route
title: Approximate a Rohlin tower cut and diagonalize every finite propagation constant
target: single-denominator-borel-cuts-have-a-rohlin-escape
requires:
  - fixed-spherical-polynomials-have-no-42nd-projection
  - finite-spherical-moments-do-not-fold-regular-double
---

# Approximate a Rohlin tower cut and diagonalize every finite propagation constant

The Rohlin lemma gives towers of height `m` with complement as small as
desired.  A consecutive block of `floor(m/42)` levels has the trace and
boundary estimates `(RBC1)--(RBC2)`.  Regularity of `mu`, continuous
approximation of measurable sets, and polynomial density give `(RBC3)`;
`(RBC4)` is the triangle inequality and invariance of the `L^2` norm.

For the diagonal statement, after `A_m` is known choose recursively
`delta_m<min(delta_(m-1)/2,1/(mA_m))`.  On the interval
`delta_(m+1)<delta<=delta_m`, use the decoder at any earlier index tending to
infinity slowly enough (for example the largest `k<=m` for which all regular
approximation errors are at most `1/k`).  Then both the intrinsic cutoff
errors and `delta A_k` tend to zero.  No quantitative rate assumption is
used.
