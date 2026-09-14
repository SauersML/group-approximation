---
rg: 2
id: countable-rf-host-from-countable-lef-host
kind: route
title: The countable residually finite host theorem is the countable LEF host theorem applied to residually finite groups
target: countable-rf-groups-embed-in-simple-kazhdan-lef-groups
requires:
  - countable-lef-groups-embed-in-simple-kazhdan-lef-groups
  - residually-finite-groups-are-lef
---

**Subsumption** (sk-verify-8, `research/artifacts/sk-review-8-2026-09-13-part1.md`, subsumption scan). Let `Γ` be a
countable residually finite group.
- By `residually-finite-groups-are-lef`, `Γ` is LEF.
- By `countable-lef-groups-embed-in-simple-kazhdan-lef-groups`, `Γ` is then a subgroup of an infinite finitely
  generated simple Kazhdan LEF group.

That is the statement of the target. The target keeps its Wilson route, `countable-rf-groups-embed-in-simple-kazhdan-lef-groups-proof`, as an independent derivation.
