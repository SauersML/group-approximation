---
rg: 2
id: every-countable-group-embeds-in-simple-fp2-via-ha2-actors
kind: route
title: Faithful [HA_2] overgroups give simple FP_2 envelopes through twisted Brin–Thompson groups
target: every-countable-group-embeds-in-a-simple-fp2-group
requires:
  - every-countable-group-lies-in-a-faithful-ha2-actor
  - ha2-actions-give-fp2-twisted-brin-thompson-groups
---

Let `H` be countable. By `every-countable-group-lies-in-a-faithful-ha2-actor`
there is `G ≥ H` of type `FP_2` with a faithful action `G ↷ S` of type
`[HA_2]`. By `ha2-actions-give-fp2-twisted-brin-thompson-groups` (FFWZ Corollary
4.14 and Theorem 3.6 with Belk–Zaremsky simplicity), `SV_G` is simple and of type
`FP_2`, and `ι_∅ : G → SV_G` is injective. So `H ≤ G ≤ SV_G` embeds in a simple
group of type `FP_2`.

The prerequisite is not evidently equivalent to the target: no argument is known
that a simple `FP_2` group carries a faithful `[HA_2]` action, so this route
could fail while the target holds.
