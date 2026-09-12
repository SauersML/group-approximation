---
rg: 2
id: one-relator-bh-via-magnus-moldavanskii-hierarchy
kind: route
title: Climb the Magnus--Moldavanskii hierarchy one Magnus-subgroup HNN extension at a time
target: one-relator-groups-satisfy-boone-higman
requires: [magnus-hnn-permanence-forces-one-relator-boone-higman, bh-embeddability-survives-magnus-subgroup-hnn]
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

`magnus-hnn-permanence-forces-one-relator-boone-higman` is the established
implication "(M) implies every one-relator group embeds in a finitely presented
simple group". `bh-embeddability-survives-magnus-subgroup-hnn` is (M). `∎`

## What the route buys

It does not make the problem smaller. On the shift data the induction consumes,
(M) is equivalent to the target, because the HNN extension is again a
one-relator group. What it buys:

- **A base that already embeds.** The open work is concentrated in one HNN
  step, where the base `H` may be assumed to embed in a finitely presented
  simple group and the associated subgroups are free, cyclonormal and of
  decidable membership.
- **A link to the general tower route.** The same step follows from the general
  permanence premise of `boone-higman-via-decidable-edge-towers`, by
  `magnus-hnn-permanence-from-decidable-edge-permanence`. Any proof of that
  premise settles this named class at once.
