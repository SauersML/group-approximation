---
rg: 2
id: gauge-optimized-section-route-to-relative-repair
kind: route
title: Move the exact core, then round the residual induced range projection
target: bs14-relative-involution-extension-stability
requires:
  - induced-rounding-needs-rms-section-fillings
  - gauge-optimized-section-energy-controls-flexible-repair
---

Choose `(M,beta')` within a factor two of the infimum in `(GOS1)`.  Replace
the exact core of the raw tuple by `beta'`; fixed-word Lipschitzness charges
this by `O(sqrt(E_R))`.  The section-isometry calculation now has squared
intertwining energy `O(E_R)` without using individual diagram areas.

Apply the uniform finite-quotient Cayley gap, conditional expectation, and
the `1/2` spectral cut from
`induced-rounding-needs-rms-section-fillings`.  The invariant range has rank
`d+O(E_Rd)` and carries an exact endpoint representation; its compression is
`O(sqrt(E_R))` from `U[beta']`.  Add the initial core displacement.  This is
the required generalized flexible repair with one dimension-free modulus.

