---
rg: 2
id: steinberg-schur-resonance-proof
kind: route
title: Evaluate the first corrected endpoint row at p equals 31
target: steinberg-schur-antidiagonal-resonates
requires:
  - steinberg-schur-corrected-endpoint-reduction
---

Substitute `j=3` in `(SCE9)`.  The lower-Pascal sum has only `v=2` and is
`binom(2,1)q_2=2q_2`; the antidiagonal sum begins with `v=p-3` and has
coefficient `-(2^5-1)`.  Since `2^5-1=31=0` in `F_31`, `(SAR1)` loses its
high endpoint coefficient exactly.
