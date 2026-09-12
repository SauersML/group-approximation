---
rg: 2
id: boone-higman-via-enlarged-shell-stabilizers
kind: route
title: Enlarge both the shell actor and its stabilizer to obtain a faithful type A action
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-fp-groups-embed-in-perfect-decidable-fp-groups
  - perfect-shell-actions-have-fp-permutation-extensions
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/boone-higman-enlarged-digit-fiber-stabilizer-2026-09-08.md
---

Given a finitely generated decidable G, Clapham and the perfect
wrapper embed it in an infinite perfect decidable finitely presented
P. Apply the OPEN extension hypothesis to obtain E_nu<=Gamma and K.
The Gamma/K action is faithful by core-freeness, has finitely
generated stabilizers by conjugacy with K, and has finitely many
orbits of pairs by finite bi-index. Gamma is finitely presented.

Thus the action has type (A), and the required theorem embeds
Gamma in a finitely presented simple group. The chain through
P and E_nu embeds G there. The missing universal construction is
exactly the named extension hypothesis; the digit model only
establishes a restricted positive case of it.
