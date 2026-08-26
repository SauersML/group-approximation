---
rg: 2
id: induce-rank-one-coadjoint-character-over-last-kernel
kind: route
title: Induce a rank-one coadjoint character over the last congruence kernel
target: rank-one-last-layer-induced-tower-avoids-six-root-carrier
requires: []
---

Identify the last kernel of `SL_3(Z/2^a Z)` with the additive group
`sl_3(F_2)` and induce the character paired with `E_12`.  Normality makes the
induced character vanish outside that kernel, proving canonical fixed-word
convergence.  Conjugation reduces the character calculation to the 21
incident point-hyperplane pairs `(u,v)` with `v^Tu=0`.

The rank-one condition excludes the all-negative six-sign atom.  Directly
counting the pairs for which both `u` and `v` have odd coordinate sum gives
six negative and fifteen positive values for the full parity word, hence
normalized trace `3/7`.  This simultaneously proves carrier absence and
the macroscopic moving parity coefficient.
