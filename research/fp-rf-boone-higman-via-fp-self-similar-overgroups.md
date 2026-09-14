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
---

Let `G` be finitely presented and residually finite. The open clause gives a
finitely presented self-similar `H <= Aut(T_d)` with `G <= H`. Zaremsky's
theorem embeds `H` in a finitely presented simple group, and restriction
embeds `G` there as well.

Nothing else is needed: the simple group is produced by the imported theorem,
and no permutation action, maximal kernel, germ group or ring is involved.
The residual finiteness hypothesis is forced by the method, since every
subgroup of `Aut(T_d)` is residually finite.
