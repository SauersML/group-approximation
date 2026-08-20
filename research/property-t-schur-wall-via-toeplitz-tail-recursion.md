---
rg: 2
id: property-t-schur-wall-via-toeplitz-tail-recursion
kind: route
title: Place the packet across the Toeplitz head and recurse on every residual erasure
target: schur-packet-as-positive-density-compressor-wall
requires:
  - schur-child-crosses-toeplitz-compressor
  - residual-action-can-erase-local-reynolds-density
  - toeplitz-tail-retains-contextual-schur-density
  - non-ce-bcs-has-robust-approximate-energy-gap
  - finite-schur-clifford-packet-flexible-hs-exactification
  - contractive-computation-ladder
---

The robust BCS gap supplies positive total forbidden carrier mass. Exactify
the fixed Toeplitz-head packet and apply the dichotomy in
`toeplitz-tail-retains-contextual-schur-density`. A surviving head component
is the projection `W` required by the target. If the residual compressed
action consumes it, the same contextual carrier is recreated one level down
with a fixed contraction and fixed HS cost. The contractive ladder sums all
tail costs. The residual-erasure theorem is included as a prerequisite to
make explicit that local subgroup placement alone is not being used as the
missing inference.

