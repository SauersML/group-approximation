---
rg: 2
id: balanced-schur-finite-depth-regular-absorption-proof
kind: route
title: Absorb every charged level into a finite vertex packet and match regular edge restrictions
target: balanced-schur-finite-depth-reuse-is-regular-absorbed
requires:
  - agent-first-hit-finite-fresh-tree-has-marked-matrix-model
  - agent-first-hit-one-schur-two-cell-is-regular-absorbed
  - proper-corner-charged-section
---

The balanced Schur square and auxiliary sign flip enlarge each level only to
a finite semidirect vertex packet.  Dressing the proper Reynolds path uses
the same HNN letter and creates no cross-edge relation.  Every reuse and
first-hit row is therefore still an isomorphism of marked finite edge
groups.  For a common multiple `L`, the negative regular packets
`(L/|F_v|)lambda^-_(F_v)` restrict on every incident marked edge `E` as the
same packet `(L/|E|)lambda^-_E`; hence all rows admit exact intertwiners and
the common payload sign remains `-I`.
