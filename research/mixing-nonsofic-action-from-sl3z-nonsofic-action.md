---
rg: 2
id: mixing-nonsofic-action-from-sl3z-nonsofic-action
kind: route
title: A nonsofic action of SL3(Z) becomes a free mixing nonsofic action through the Howe-Moore envelope SL3(R)
target: mixing-free-nonsofic-action-of-sofic-group
requires:
  - sl3z-admits-nonsofic-action
  - howe-moore-lattice-nonsofic-action-transfers-to-mixing
  - howe-moore-property-for-simple-lie-and-p-adic-groups
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-part2-2026-09-12.md
---

Conditional route: it fires exactly when `sl3z-admits-nonsofic-action` is established.

1. `SL_3(R)` is a connected, noncompact, simple real Lie group with finite center, so it has the
   Howe--Moore property (`howe-moore-property-for-simple-lie-and-p-adic-groups`).
2. `SL_3(Z)` is a lattice in `SL_3(R)` (Borel--Harish-Chandra; the standard example, Furman,
   arXiv:0901.0678, p. 5).
3. If `SL_3(Z)` has a nonsofic p.m.p. action, then `SL_3(Z) ∉ 𝒮`. The dichotomy of
   `howe-moore-lattice-nonsofic-action-transfers-to-mixing` then gives an essentially free, mixing,
   nonsofic action, explicitly `SL_3(Z) ↷ SL_3(R) ×_(SL_3(Z)) (Z × {0,1}^(SL_3(Z)))` for an ergodic
   nonsofic seed `Z`.
4. `SL_3(Z)` is residually finite, since reduction mod `p` separates any nonidentity element from `1`
   for large `p`. So it is sofic: permutation actions on finite quotients in which a given finite set
   injects are sofic approximations.

So `SL_3(Z)` witnesses `mixing-free-nonsofic-action-of-sofic-group`. The same argument works with
`SL_3(Z)` replaced by any finitely generated lattice of a group in
`howe-moore-property-for-simple-lie-and-p-adic-groups` (part 2 artifact, Corollary MT2 and the
remark after it).
