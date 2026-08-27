---
rg: 2
id: toeplitz-child-section-dichotomy-proof
kind: route
title: Expand the square of a compressed Toeplitz return
target: toeplitz-child-section-loses-square-or-exit
requires:
  - binary-schur-child-toeplitz-self-embedding
  - projective-gauge-charge-forces-morita-or-corner
---

# Expand the square of a compressed Toeplitz return

Insert `1=p+(1-p)` between the two occurrences of `h` to obtain `(TSE4)`.
Expand the two corner Gram operators to obtain `(TSE6)` and its adjoint
analogue. If both vanish, the off-diagonal row and column vanish and `p`
reduces `h`. Formula `(TSE8)` is the trace of `(TSE6)`. The off-diagonal
two-block model proves that `h^2=J` does not bound the compression leakage.
The final coefficient-isometry assertion is the unitary identity
`||1-XY||_2=||1-YX||_2`.
