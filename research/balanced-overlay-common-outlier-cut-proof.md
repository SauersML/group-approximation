---
rg: 2
id: balanced-overlay-common-outlier-cut-proof
kind: route
title: Apply spectral coarea to the balanced covariant defect square function
target: balanced-overlay-common-reducing-outlier-cut
requires:
  - raw-relator-square-function-is-automatically-covariant
  - covariant-square-function-has-common-reducing-threshold
---

Use the raw balanced residual square function in `(CSF1)`.  Its trace is
`O(E)` and `raw-relator-square-function-is-automatically-covariant` gives
covariance `O(sqrt(E))`.  Equations `(CSF2)`--`(CSF3)` give the common threshold and
the simultaneous block-diagonal correction.  Because the inputs are
self-adjoint involutions, take the spectral signs of the two self-adjoint
diagonal compressions; the cosine--sine estimate controls this extra polar
step and yields the block-diagonal reflections stated in `(BRC1)`.
