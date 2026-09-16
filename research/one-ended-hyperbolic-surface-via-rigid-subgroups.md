---
rg: 2
id: one-ended-hyperbolic-surface-via-rigid-subgroups
kind: route
title: A one-ended hyperbolic group has a surface subgroup or a quasiconvex infinite rigid subgroup, and the rigid case supplies a surface subgroup
target: one-ended-hyperbolic-groups-contain-surface-subgroups
requires:
  - one-ended-hyperbolic-groups-contain-surface-or-rigid
  - rigid-hyperbolic-groups-contain-surface-subgroups
---

Let `Gamma` be a one-ended hyperbolic group.

- By `one-ended-hyperbolic-groups-contain-surface-or-rigid`, `Gamma` contains a surface subgroup
  with `chi < 0`, and then we are done, or an infinite quasiconvex subgroup `R` admitting no
  nontrivial splitting over a finite or virtually cyclic subgroup.
- Quasiconvex subgroups of hyperbolic groups are finitely generated and hyperbolic (standard). So
  `R` is an infinite hyperbolic group with no such splitting.
- By `rigid-hyperbolic-groups-contain-surface-subgroups`, `R` contains the fundamental group of a
  closed surface with `chi < 0`. That is a subgroup of `Gamma`.

**Converse.** The route loses nothing:
- the root trivially implies the first requirement;
- the root implies the second, because an infinite rigid group is one-ended by Stallings.

**Partial result for groups without 2-torsion.** The first requirement is proved by the imported
`wilton-no-2-torsion-surface-or-rigid-subgroup`. Such a group contains a surface subgroup as soon
as `rigid-hyperbolic-groups-contain-surface-subgroups` holds.
