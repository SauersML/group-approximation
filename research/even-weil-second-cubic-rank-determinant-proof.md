---
rg: 2
id: even-weil-second-cubic-rank-determinant-proof
kind: route
title: Combine the deleted-line Legendre determinant with the rank-six cubic residual
target: even-weil-second-cubic-has-a-rank-six-determinant-gap
requires:
  - even-weil-fixed-line-compression
---

For `p=5 mod 8`, the deleted fixed line has `S`-eigenvalue one and
`R`-eigenvalue `(2|p)=-1`.  The positive Fourier coefficient at zero implies
that polar rounding the compressed involution does not change its
determinant.  Comparing the full exact second cubic with the compression
therefore gives determinant `-1`.  Inserting the deleted-line projection in
the exact cubic shows that the compressed residual has rank at most three;
the polar rank-one change adds at most three more.  A rank-`r` unitary
residual with determinant `-1` has unnormalized Frobenius norm at least
`2/sqrt(r)`, giving the claimed `p^(-1/2)` normalized lower bound.
