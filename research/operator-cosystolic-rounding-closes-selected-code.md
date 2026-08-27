---
rg: 2
id: operator-cosystolic-rounding-closes-selected-code
kind: route
title: Combine repeated LDPC Weyl sampling with operator cosystolic rounding
target: bounded-occurrence-private-sampler-additive-decoder
requires:
  - repeated-good-ldpc-coordinates-give-private-weyl-sampler
  - quadratic-repetition-supports-complete-commutation-overlay
  - operator-unique-neighbor-cosystolic-rounding
---

Apply the operator cosystolic correction separately to the repeated X and Z
occurrence systems.  It produces exact additive code actions on the original
Hilbert space.  The private Weyl matching then invokes the established
matrix-dimension gap, while the complete overlay rules out exact contextual
quotients before correction.  Fixed private basins transfer the correction
to the mixed roots with constant loss.

This route closes the analytic selected-code decoder only.  The complete
logical pair overlay can still create contours through several distinct
private basins, so finite-presentation word placement remains a separate
compiler condition and is not inferred from operator cosystolic expansion.
