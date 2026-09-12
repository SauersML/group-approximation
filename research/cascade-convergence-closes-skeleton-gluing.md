---
rg: 2
id: cascade-convergence-closes-skeleton-gluing
kind: route
title: Rigidity plus syzygy plus cascade convergence give the skeleton gluing
target: skeleton-relative-hs-stability-for-sl2
requires:
  - bs14-exact-representation-variety-is-hs-locally-rigid
  - solenoid-absorption-cascade-converges
---

Levit--Vigdorovich stability exactifies both parabolic skeletons (both
are `BS(1,4)`).  `bs14-exact-representation-variety-is-hs-locally-rigid`
aligns them to share one exact `h` with a small conjugator.  Defining
the lower tower as the swap image makes the `w(1)` relation exact and
moves all residual defect into the two swap holonomies, which the
Steinberg cocycle syzygy `w(s)w(t)^{-1}=h(s/t)` collapses to a single
twisted-coboundary equation on the commutant torsor.
`solenoid-absorption-cascade-converges` solves that equation with
dimension-free loss.  The corrected tuple satisfies every defining
relation of `SL_2(Z[1/2])` exactly up to `o(1)`, i.e. it is HS-close to
an exact representation relative to the skeleton data -- the target.
