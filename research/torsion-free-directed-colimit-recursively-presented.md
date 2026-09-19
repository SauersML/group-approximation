---
rg: 2
id: torsion-free-directed-colimit-recursively-presented
kind: claim
title: Every torsion-free group is a directed colimit of finitely generated recursively presented torsion-free groups
distinct_from:
  torsion-free-universal-quotient-recursively-presented: that constructs the universal torsion-free quotient of one recursively presented group; this uses that construction functorially on finite presentation approximants of an arbitrary torsion-free group.
  whitehead-class-supported-on-finitely-generated-subgroup: that is an elementwise finite-support statement about one Whitehead class; this is a group-level directed-colimit decomposition.
---

Every torsion-free group `G` is a directed colimit

```text
G = colim_i K_i
```

where every `K_i` is finitely generated, recursively presented, and
torsion-free. The structure maps need not be injective.

The construction takes finite presentation approximants `P_i` of `G`
and replaces each one functorially by its universal torsion-free quotient
`P_i^tf`. The nontrivial point is that the resulting colimit is still
`G`, not merely some torsion-free group mapping to `G`. This is an
existence theorem; when `G` is not recursively presented, the directed
system is not asserted to be effectively enumerable.

**ESTABLISHED 2026-08-30** by
[[torsion-free-directed-colimit-via-universal-quotients]].
