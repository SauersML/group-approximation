---
rg: 2
id: no-finitely-generated-group-contains-all-fg-rf-groups-proof
kind: route
title: A finitely generated group has countably many finitely generated subgroups, but there are uncountably many finitely generated residually finite groups
target: no-finitely-generated-group-contains-all-fg-rf-groups
requires:
  - chong-wise-uncountably-many-fg-residually-finite-groups
---

- A finitely generated group `U` is countable, so it has countably many finite subsets, hence countably many finitely
  generated subgroups.
- By `chong-wise-uncountably-many-fg-residually-finite-groups` there are uncountably many pairwise nonisomorphic
  finitely generated residually finite groups.
- So some of them are not isomorphic to any subgroup of `U`. ∎
