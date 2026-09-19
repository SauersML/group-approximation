---
rg: 2
id: sl3-arithmetic-double-fold-proof
kind: route
title: Apply finite-dimensional co-density to the block-swap intertwiner
target: sl3-arithmetic-double-finite-representations-fold
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

For a representation of `D=A*_C A`, place its two vertex restrictions
`pi_0,pi_1` on the diagonal of one representation
`rho=pi_0 direct_sum pi_1` of `A`.  Their equality on `C` says that the
block-swap unitary belongs to `rho(C)'`.  Finite-dimensional co-density
gives `rho(C)'=rho(A)'`, so the swap intertwines the two restrictions on
all of `A`.  Hence they are equal and the representation factors through
the fold `D->A`.

