---
rg: 2
id: adaptive-rectangular-kernel-column-extraction-proof
kind: route
title: Average diagonal kernel blocks and apply Markov extraction
target: adaptive-rectangular-kernel-column-extraction
requires: []
---

Write the amplified kernel projection as `P=(P_ij)` and average the mass and
return energy of its diagonal blocks.  Projection cyclicity identifies these
averages exactly with `tr(P)` and the amplified return energy.  Discard the
indices whose return energy is larger than `2epsilon^2/alpha`; Markov's
inequality discards fewer than an `alpha/2` fraction, so the surviving blocks
still have average mass at least `alpha/2`.  The square root of one surviving
diagonal block is the required original-model contraction.  Cyclic shifts
with their one-dimensional fixed space give the vanishing-density
calibration.  Thresholding that positive contraction at `sqrt(alpha)/2`
retains trace at least `alpha/(4-alpha)`; the operator inequality
`X^2>=(alpha/4)Q` transfers the return estimate to this actual projection.
