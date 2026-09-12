---
rg: 2
id: complete-overlay-global-code-pvm-proof
kind: route
title: Multiply the commuting binary spectral projections and enforce parity support
target: complete-overlay-glues-exact-ldpc-face-pvms
requires:
  - quadratic-repetition-supports-complete-commutation-overlay
  - binary-face-pvm-is-determined-by-coordinate-reflections
---

Collapse exact copies, use the pair overlay to commute all logical coordinate
reflections, and form the global atoms `(COG1)`.  Their sum is the identity by
successively expanding each binary spectral partition.  A violated parity
check would make its product act as minus one on an atom although the exact
relation makes it act as plus one, so that atom vanishes.  Binary Fourier
reconstruction identifies every given face PVM with the corresponding
marginal.
