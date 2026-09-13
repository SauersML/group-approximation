---
rg: 2
id: fp-rf-boone-higman-via-fp-self-similar-overgroups
kind: route
title: Embed the residually finite input in a finitely presented self-similar group and apply Zaremsky
target: fp-residually-finite-boone-higman
requires:
  - every-fp-rf-group-embeds-in-fp-self-similar-group
  - fp-self-similar-groups-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
  - research/artifacts/regular-tree-torsion-obstruction-2026-09-12.md
---

Let `G` be finitely presented and residually finite. The open clause gives a finitely presented self-similar `H <= Aut(T_d)` with `G <= H`. Zaremsky's theorem embeds `H` in a finitely presented simple group, and restriction embeds `G` there as well.

Nothing else is needed: the simple group comes from the imported theorem, and no permutation action, maximal kernel, germ group or ring is involved. The residual finiteness hypothesis is forced by the method, since every subgroup of `Aut(T_d)` is residually finite.

**Obstruction.** Any finitely presented residually finite group that acts faithfully on no regular rooted tree refutes the open clause (`some-fp-rf-group-acts-on-no-regular-rooted-tree`).
- A finitely presented residually finite overgroup of the two-generated group in `cycle-transposition-lef-group-has-no-regular-tree-action` would supply such a group.
- The general residually finite Higman embedding theorem would have supplied one, but it is false (`rf-higman-embedding-for-decidable-groups-fails`; Rauzy, arXiv:2002.02540, Theorem 1).
- Rauzy's obstruction is failure of effective residual finiteness. It does not apply to that effectively residually finite group.
- So whether this route is compatible with such an overgroup remains open.
