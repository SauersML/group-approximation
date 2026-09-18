---
rg: 2
id: faithful-ha2-actor-via-orbit-finite-fp2-affine-actors
kind: route
title: "Orbit-finite FP_2 affine overgroups are faithful [HA_2] overgroups"
target: every-countable-group-lies-in-a-faithful-ha2-actor
requires:
  - every-countable-group-embeds-in-an-orbit-finite-fp2-affine-actor
  - orbit-finite-fp2-affine-actors-are-faithful-ha2-actors
---

Let `G` be countable. By `every-countable-group-embeds-in-an-orbit-finite-fp2-affine-actor`
it embeds in `Γ = S ⋊ W`, of type FP_2, with `W ≤ Aut(S)` finitely generated and
finitely many `W`-orbits on `S`. By case (A) of
`orbit-finite-fp2-affine-actors-are-faithful-ha2-actors`, the affine action
`Γ ↷ S` is faithful and of type `[HA_2]`. So `G` lies in the FP_2 group `Γ` with
a faithful `[HA_2]` action, which is the target.

The single open prerequisite fails on its own: it can fail at test case 3
(`Q/Z`) while the target still holds through a non-affine actor.
