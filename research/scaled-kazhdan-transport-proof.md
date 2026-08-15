---
rg: 2
id: scaled-kazhdan-transport-proof
kind: route
title: Rescale the capture step; reuse the corner and equal-rank flip verbatim
target: scaled-kazhdan-transport
requires: []
artifacts:
  - GroupApproximation/Sofic/ScaledKazhdanTransport.lean
---

The Kazhdan corner, its displacement bounds, and the equal-rank projection
flip are operator-norm statements on the adjoint model and are reused
unchanged.  Only spectral capture and the final bookkeeping see the
weight: replacing the operator-norm bound on the commutant sequence by a
Frobenius-mass bound `O(w n)` makes the AM--GM energy estimate scale with
`w n` on both sides, and the dimension-free vector chain finishes.
Kernel-checked end to end.
