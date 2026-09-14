---
rg: 2
id: rf-host-from-lef-host
kind: route
title: The residually finite embedding theorem is the LEF embedding theorem applied to residually finite groups
target: rf-groups-embed-in-simple-kazhdan-lef-groups
requires:
  - lef-groups-embed-in-simple-kazhdan-lef-groups
  - residually-finite-groups-are-lef
---

**Subsumption** (sk-verify-8 part1, subsumption scan). Let `Γ` be a finitely generated residually finite group.
- By `residually-finite-groups-are-lef`, `Γ` is LEF.
- By `lef-groups-embed-in-simple-kazhdan-lef-groups`, `Γ` is then a subgroup of an infinite finitely generated simple
  Kazhdan LEF group.

That is the statement of the target. The target keeps its Toeplitz route, `rf-groups-embed-in-simple-kazhdan-lef-groups-proof`, as an independent derivation.
