---
rg: 2
id: countable-lef-groups-embed-in-simple-kazhdan-lef-groups
kind: claim
title: A countable group is LEF iff it is a subgroup of an infinite finitely generated simple Kazhdan LEF group
distinct_from:
  lef-groups-embed-in-simple-kazhdan-lef-groups: that is the finitely generated case; this is the countable case, reduced to it by the 2-generator LEF embedding.
  countable-rf-groups-embed-in-simple-kazhdan-lef-groups: that is the residually finite case through Wilson's theorem; this covers all countable LEF groups, e.g. derived topological full groups and the groups G_X themselves.
artifacts:
  - research/artifacts/sk-universal-lef-host-b-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Route: `countable-lef-groups-embed-in-simple-kazhdan-lef-groups-proof`.

A countable group is LEF if and only if it embeds in an infinite, finitely generated, simple group with property (T)
that is LEF, and so sofic and hyperlinear.

- ⇐: subgroups of LEF groups are LEF, since the definition only involves finite subsets.
- ⇒: `Γ × Z` is countable, infinite and LEF (products of partial models). It lies in a 2-generated infinite LEF group
  (`countable-lef-groups-embed-in-two-generator-lef-groups`), which lies in an infinite f.g. simple Kazhdan LEF group
  (`lef-groups-embed-in-simple-kazhdan-lef-groups`).

This extends the reviewed f.g. characterization to countable groups at the cost of one lemma.
