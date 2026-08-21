---
rg: 2
id: gcc-via-multiscale-hexagon-holonomy
kind: route
title: Iterate the scale-free A2 holonomy-or-leakage recurrence at fixed depth
target: commuting-conjugate-involution-transfer-for-sl3-pair
requires:
  - six-edge-holonomy-energy-ledger-is-scale-free
  - arithmetic-hexagon-decoding-or-conductor-leakage
---

Apply the decoded hexagon at each of the first `N` conductor levels.  The
scale-free holonomy ledger charges every positive nonleaking interior-overlap
sector, while the decoder sends every uncharged exit into the next conductor
layer and the Weyl/property-T packet removes a fixed fraction.  Iteration
gives `(AHD3)`.

For fixed `N`, canonical microstates make the finite presentation and trace
errors tend to zero.  Then let `N` tend to infinity.  The interior overlap
energy vanishes, forcing the commuting conjugate projection overlap to an
endpoint.  This is exactly
`commuting-conjugate-involution-transfer-for-sl3-pair`.
