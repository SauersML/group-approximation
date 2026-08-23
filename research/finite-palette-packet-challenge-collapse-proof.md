---
rg: 2
id: finite-palette-packet-challenge-collapse-proof
kind: route
title: Color packet states by a finite operator-norm cover and collide one edge
target: finite-palette-packet-challenge-collapse
requires:
  - opnorm-packet-collision-kills-phase
artifacts:
  - GroupApproximation/Sofic/CollisionCapacityDetectors.lean
---

Compose the state assignment `v |-> B_v` with the palette coloring.  By the
challenge hypothesis there is an adjacent monochromatic pair.  The
same-color diameter bound makes this pair `delta`-close.  Apply
`opnorm-packet-collision-kills-phase` to its local and cross checks.

For matrices, a finite palette exists because `U(d)` is compact in operator
norm.  No estimate for the palette size is needed; only finiteness matters.
