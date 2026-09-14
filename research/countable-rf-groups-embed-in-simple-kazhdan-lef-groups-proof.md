---
rg: 2
id: countable-rf-groups-embed-in-simple-kazhdan-lef-groups-proof
kind: route
title: Embed the countable group in a 2-generator residually finite group (Wilson), then take its Kazhdan LEF envelope
target: countable-rf-groups-embed-in-simple-kazhdan-lef-groups
requires:
  - wilson-countable-rf-into-two-generator-rf-groups
  - rf-groups-embed-in-simple-kazhdan-lef-groups
artifacts:
  - research/artifacts/sk-strong-1-universal-kazhdan-group-2026-09-13.md
---

Let `G` be countable and residually finite.
1. By `wilson-countable-rf-into-two-generator-rf-groups`, `G ≤ Ĝ` for a 2-generator residually finite
   group `Ĝ`.
2. By `rf-groups-embed-in-simple-kazhdan-lef-groups`, applied to the finitely generated residually finite group `Ĝ`,
   there is an infinite, finitely generated, simple Kazhdan LEF group `U ≥ Ĝ`.
3. So `G ≤ U`. ∎

Nothing else is used. Subgroups of LEF groups are LEF, so every finitely generated subgroup of `G` is LEF, as it must be.
