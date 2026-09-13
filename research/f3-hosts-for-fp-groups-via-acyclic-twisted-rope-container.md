---
rg: 2
id: f3-hosts-for-fp-groups-via-acyclic-twisted-rope-container
kind: route
title: "An FP_3 acyclic-host twisted rope container of a universal group is an F_3 host of every finitely presented group"
target: every-finitely-presented-group-embeds-in-an-f3-group
requires:
  - acyclic-host-twisted-rope-container-is-of-type-fp3
---

The required claim gives a container `K_ac(G)` of type `FP_3`, where `G` is
finitely presented, acyclic and contains a universal finitely presented group.

- `K_ac(G)` is finitely presented. This is item 1 of the required claim,
  derived in `research/artifacts/zp-z1-01-ffz-fp3-level-three-2026-09-13-part2.md`
  from the finite relations of `P_0` and `G` and the conjugation relations for
  the generators of `L`.
- A finitely presented group of type `FP_3` is of type `F_3`
  (Fournier-Facio–Zaremsky arXiv:2607.21727v1, Lemma 2.1).
- `K_ac(G)` contains `G`, hence a universal finitely presented group, hence
  every finitely presented group.

**Dead end.** The required claim is refuted by
`acyclic-host-twisted-rope-container-is-never-fp3`, so this route never fires.
It is kept because the implication is true and records the attempt.
