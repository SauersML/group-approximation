---
rg: 2
id: fp-bvc-vc-via-excluding-vc-splittings
kind: route
title: Split over a virtually cyclic subgroup or be finite
target: finitely-presented-bvc-groups-are-virtually-cyclic
requires:
  - bvc-groups-splitting-over-vc-subgroups-are-vc
  - fp-bvc-groups-without-vc-splittings-are-finite
---

Let `G` be finitely presented with property BVC.

- If `G` has a nontrivial one-edge splitting over a virtually cyclic subgroup (an amalgam
  `A *_C B` with `C` proper in both factors, or an HNN extension with virtually cyclic
  associated subgroups), then `G` is virtually cyclic by
  `bvc-groups-splitting-over-vc-subgroups-are-vc`.
- Otherwise `G` is finite by `fp-bvc-groups-without-vc-splittings-are-finite`, hence virtually
  cyclic.

The first requirement is proved without finite generation. The whole difficulty of the
conjecture sits in the second, where an infinite group has no splitting over a virtually
cyclic subgroup. By Stallings' theorem (quoted from memory, not used in the argument) such a
group is one-ended.
