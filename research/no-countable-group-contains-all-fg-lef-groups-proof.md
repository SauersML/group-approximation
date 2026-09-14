---
rg: 2
id: no-countable-group-contains-all-fg-lef-groups-proof
kind: route
title: A countable group has countably many finitely generated subgroups, and the G_X realize continuum many isomorphism types
target: no-countable-group-contains-all-fg-lef-groups
requires: [continuum-many-simple-kazhdan-lef-groups]
---

1. **Countably many f.g. subgroups.** A countable group `H` has countably many finite subsets, so countably many
   finitely generated subgroups. Hence at most countably many isomorphism types of f.g. groups embed in `H`.
2. **Continuum many types.** By `continuum-many-simple-kazhdan-lef-groups`, the infinite f.g. simple Kazhdan LEF groups
   `S_X` (over `F_2`, `S_X = G_X`) realize continuum many isomorphism types.
3. **Conclusion.** No countable `H` contains every `G_X`. Each `G_X` is finitely generated and LEF, so no countable `H`
   contains every f.g. LEF group. ∎
