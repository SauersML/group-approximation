---
rg: 2
id: simple-kazhdan-lef-host-iff-lef-and-countably-many-types-proof
kind: route
title: Subgroups of LEF groups are LEF, countable groups have countably many f.g. subgroups, and the family host supplies (3) ⇒ (1)
target: simple-kazhdan-lef-host-iff-lef-and-countably-many-types
requires: [simple-kazhdan-lef-host-for-recursive-lef-groups, no-countable-group-contains-all-fg-lef-groups]
artifacts:
  - research/artifacts/sk-universal-lef-host-a-2026-09-13.md
---

Artifact §4.

1. **(1) ⇒ (2).** A finitely generated group is countable.
2. **(2) ⇒ (3).**
   - LEF passes to subgroups: restrict partial models to finite subsets of the subgroup.
   - A countable group has countably many finite subsets, so countably many finitely generated subgroups. So it meets at most countably many isomorphism types.
3. **(3) ⇒ (1).** Choose one member of each isomorphism type. This is a countable set of countable LEF groups, so part (a) of `simple-kazhdan-lef-host-for-recursive-lef-groups` gives one host containing all of them.
4. **Examples.**
   - Finitely generated linear groups are residually finite (Mal'cev), hence LEF, and countable up to isomorphism: finitely many matrices over the finitely generated field of their entries, and finitely generated fields have countably many isomorphism types.
   - F.g. groups with solvable word problem have recursive relator sets, and there are countably many.
   - The set of all f.g. LEF groups fails (2), by `no-countable-group-contains-all-fg-lef-groups`. □
