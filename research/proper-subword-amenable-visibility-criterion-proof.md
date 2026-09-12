---
rg: 2
id: proper-subword-amenable-visibility-criterion-proof
kind: route
title: Apply Linton's free-product kernel theorem to the retained Weinbaum packet
target: proper-subword-amenable-visibility-criterion
requires: []
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Replace `Q` by `phi(G)`, which remains amenable and locally indicable.  Linton,
*Residually rationally solvable one-relator groups*, arXiv:2407.09272v2,
Theorem 3.2, applies exactly to this data.  It says that `ker(phi)` is a free
product of a free group, subgroups of `A`, subgroups of `B`, and copies of
`Z/mZ`.

Every subgroup of either free factor is free by Nielsen--Schreier.  Hence
`ker(phi)` is a free product of free and finite cyclic groups and is sofic.
The quotient `phi(G)` is amenable, so the standard theorem that a group with
sofic kernel and amenable quotient is sofic proves the claim.

No closure under a general sofic-by-sofic extension is used.
