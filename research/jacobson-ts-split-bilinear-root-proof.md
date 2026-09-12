---
rg: 2
id: jacobson-ts-split-bilinear-root-proof
kind: route
title: Split the three TS conjugates and transport both finite stabilizers through the first braid
target: jacobson-mixed-cells-reconstruct-full-first-level-root-packet
requires:
  - jacobson-boundary-cell-reconstructs-finite-root-packet
artifacts:
  - research/artifacts/jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md
---

The finite boundary packet gives `[u,D_i]=a_i` and
`D_3=D_1D_2`. Expand the three conjugate TS commutators to obtain
`[u,h r h]=D_i r D_i`. Comparing these three equations makes all
`D_i` commute with `r`, and leaves the pure tail commutator equal
to `r`. The same comparison with errors gives the stated constants.

Write `b=q_Q q_P`. Since `b a_1 b=x_31,Q` centralizes `h`,
two braid substitutions prove `[b,D_1]=1`. Combining this with the
new TS commutation and the original boundary identities yields all
generators of the tail point stabilizer and head covector stabilizer.
The resulting orbit is indexed by pairs `(v,f)`.

Transport the two addition laws already present in the boundary packet
across these finite orbits. Expanding one two-variable sum in the two
orders and cancelling the outside factors gives every cross
commutation. The literal action distinguishes all nine binary matrix
coordinates and separates them from the level-preserving original
packet. It proves injectivity of the claimed semidirect product.
