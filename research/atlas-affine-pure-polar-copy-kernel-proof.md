---
rg: 2
id: atlas-affine-pure-polar-copy-kernel-proof
kind: route
title: Compute the common kernel of all pure collision-polar copies
target: atlas-affine-collision-collapses-pure-polar-copies
requires:
  - atlas-affine-acute-angle-forces-two-point-k-orbit
---

For the unique nonzero affine residual, selfadjointness gives
`R_c=-2Q`, `|R_c|=2Q`, and polar partial isometry `V_c=-Q`.  Thus its initial
and final high spaces coincide and every supported word in `Q,V_c,V_c^*` is
a scalar multiple of `Q`.  Every duplicated or postprocessed pure-polar map
therefore factors through `QP`.

The Reynolds calculation identifies `rank(P)/d=1-1/|L|`.  In the elementary
abelian translation module, orbit size three forces `|L|>=4`, while orbit
size six forces `|L|>=8`.  Since `rank(Q)=d/2`, the Grassmann dimension
inequality leaves a common kernel of dimension at least `d/4`, respectively
`3d/8`.  This proves the claimed obstruction and isolates external
pretransport as the only bounded-copy escape.
