---
rg: 2
id: gauge-optimized-energy-closes-flexible-boundary
kind: route
title: Use optimized induced energy to pay the flexible BS boundary
target: bs14-flexible-cross-packet-boundary-reconciliation
requires:
  - gauge-optimized-induced-energy-target
  - uniform-gauge-optimized-induced-energy
  - regular-bs14-cores-admit-dyadic-one-power-shadows
---

Apply `(UGO1)` after the regular dyadic one-power preconditioner.  The
induced projection rounding in `(GOI6)` changes generators by the square
root of the normalized presentation energy and changes rank by at most a
constant times that energy.  In unnormalized Frobenius notation this gives
`k<=CE`, exactly `(FBR2)--(FBR3)`.  The exact compression is a common
endpoint, so the same boundary repairs both cubic constraints rather than
rounding them independently.
