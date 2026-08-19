---
rg: 2
id: scale-index-route
kind: route
title: Scale-index route through commutant reconstruction
target: non-hyperlinear-group
requires: [quantized-scale-index]
artifacts:
  - notes/TRUE_LOCALLY_FINITE_COMMUTANTS_RECOVER_BUT_AT_SHIFTED_SCALES.md
---

Successor of the ruled-out separate-recovery route separate-commutant-recovery. Coordinate
commutant recovery works elementwise via Reynolds averaging (shifted-scale-recovery); the
compressor shifts the exhaustion scale exactly (for the unilateral binary
shift, `dim(D_m) = 2·dim(C_{m+1})`). A quantized scale index or two-branch
scale synchronization (quantized-scale-index) turns that exact mismatch into a
contradiction with the microstate trace, refuting hyperlinearity of the
candidate.
