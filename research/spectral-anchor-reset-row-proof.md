---
rg: 2
id: spectral-anchor-reset-row-proof
kind: route
title: Reset one commuting spectral block and expand its commutator row
target: spectral-cut-anchor-reset-pays-boundary-in-one-row
requires:
  - localized-loewner-pays-spike-or-boundary
---

Since `p` commutes with `A`, `(SAR1)` is block diagonal with reflections
`1` and `qAq`, proving involutivity and `(SAR2)`.  Expand `[A',B]` in the
`p+q` blocks.  Its `q-q` block is `q[A,B]q`; every off-diagonal block is a
contraction times `pBq` or `qBp`, whose combined Hilbert--Schmidt norm is
controlled by `[p,B]`.  This proves `(SAR3)` and, after the weighted
two-term square inequality, `(SAR4)`.  Telescope bounded faces and count
the balanced incidences of one shared coordinate.
