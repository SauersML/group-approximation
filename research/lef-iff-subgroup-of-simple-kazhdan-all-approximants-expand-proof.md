---
rg: 2
id: lef-iff-subgroup-of-simple-kazhdan-all-approximants-expand-proof
kind: route
title: The LEF host, quotients by maximal normal subgroups, and openness of (T)
target: lef-iff-subgroup-of-simple-kazhdan-all-approximants-expand
requires: [lef-groups-embed-in-simple-kazhdan-lef-groups, simple-lef-groups-are-limits-of-finite-simple-groups, kazhdan-marked-limits-eventually-uniform-expanders]
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md
---

- **(2) ⇒ (1).** LEF passes to subgroups, and a marked limit of finite groups is LEF.
- **(1) ⇒ (2).**
  - `lef-groups-embed-in-simple-kazhdan-lef-groups` gives an infinite f.g. simple Kazhdan LEF host `G ⊇ Γ`.
  - `simple-lef-groups-are-limits-of-finite-simple-groups` makes `G` a marked limit of finite simple groups.
  - `kazhdan-marked-limits-eventually-uniform-expanders` makes every finite approximation of `(G, T)` eventually expand.
- Artifact part 1, Corollary B2.
