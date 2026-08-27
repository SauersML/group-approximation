---
rg: 2
id: affine-membership-trace-mismatch-proof
kind: route
title: Compare the conjugation-name trace with the quotient IRS trace for a Dirac normal subgroup
target: affine-haar-membership-does-not-promote-irs-trace
requires:
  - affine-haar-process-fourier-modulus-compiler
---

For a normal subgroup `N`, conjugation fixes its indicator, so the entire
translate-name probability algebra is scalar and its crossed product is
`L(Gamma)`.  The canonical trace there evaluates a nonidentity group unitary
to zero.

The stabilizer character of `delta_N` is `1_N`; its GNS representation is the
left regular representation of `Gamma/N`.  Hence every nonidentity
`n in N` has trace zero in the first canonical representation and trace one
in the second.  Meanwhile the deterministic name law is a singleton affine
coset and all its Fourier moments have modulus one.  These three direct
computations prove the claim.

