---
rg: 2
id: bs14-mixed-norm-newton-threshold-proof
kind: route
title: Combine singular-value counting with the valid operator-HS Taylor estimate
target: bs14-thresholded-newton-needs-coordinate-basin
requires:
  - iwahori-uniform-infinitesimal-rigidity
  - normalized-hs-taylor-remainder-is-not-dimension-free
  - bs14-low-rank-boundary-surgery-preserves-the-regular-face
---

Chebyshev's singular-value inequality gives `(TNB1)` and functional calculus
gives `(TNB2)`.  The first required claim supplies the lower derivative
bound after quotienting common coboundaries.  The second supplies exactly
the mixed Hessian estimate `(TNB3)`.  Taylor expansion under `(TNB4)` gives
`(TNB5)`.

The low-rank surgery claim shows what happens if a high carrier already
comes from an exposed boundary, but it has no inverse producing that
boundary from a spectral projection of `D_i`.  Therefore no implication
from `(TNB2)` to `(TNB4)` occurs in the established dependency chain.
