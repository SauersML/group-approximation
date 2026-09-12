---
rg: 2
id: boone-higman-via-shell-stabilizer-overgroups
kind: route
title: Enlarge a shell envelope while retaining a core-free stabilizer of finite bi-index
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - decidable-fp-groups-embed-in-perfect-decidable-fp-groups
  - perfect-shell-pairs-have-finite-biindex-fp-hosts
  - shell-coset-induction-preserves-core-freeness
artifacts:
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
---

Embed a finitely generated decidable G by Clapham into a decidable
finitely presented P_0, and then by the perfect-envelope theorem
into an infinite perfect decidable finitely presented P.

The OPEN host hypothesis supplies E_nu<=Gamma and the retained
shell stabilizer H of finite bi-index. The induced Gamma/H action
is faithful, has finitely generated stabilizers, and satisfies the
finite pair-orbit condition. Its actor Gamma is finitely presented.
The required induced-action theorem therefore embeds Gamma in a
finitely presented simple group, which contains G through P and E_nu.

This route does not require finite presentation of E_nu, its germ
group, or its singularity stabilizers. It requires the explicitly
unproved finite bi-index host. Abstract finite-presentation embedding
theorems alone do not supply that property.
