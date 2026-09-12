---
rg: 2
id: localized-loewner-spike-proof
kind: route
title: Test max-fractional Loewner order on an anchor times a spectral cut
target: localized-loewner-pays-spike-or-boundary
requires:
  - adjoint-parity-cone-lifts-to-loewner-order
---

Evaluate `(APL4)` on `v=Q_ap`.  Compare `P_kv` with the right-localized
physical odd vector `T_k`; their difference is a unitary translate of
`[p,Q_k]/2`.  At the selected site it vanishes because spectral projections
of `Y_(a,i)^2` commute with `Q_i`.  Square, sum, and use
`R_(a,i)>=sp`.  Splitting according to whether the boundary is at least
`kappa s tau(p)` gives the two alternatives.
