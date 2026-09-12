---
rg: 2
id: whitehead-vanishing-torsion-free-one-relator
kind: claim
title: Every subgroup of a torsion-free one-relator group has trivial Whitehead group
distinct_from:
  whitehead-vanishing-torsion-free: this covers subgroups of torsion-free one-relator groups, not the still-open assertion for every torsion-free group.
  whitehead-vanishing-finitely-presented-torsion-free: one-relator groups are finitely presented, but this theorem does not cover arbitrary finitely presented torsion-free groups.
  degree-one-assembly-surjective-torsion-free: that claim is universally quantified over all torsion-free groups; this proves its one-relator specialization.
  one-relator-groups-sofic: soficity is an approximation property and remains open for one-relator groups; Whitehead vanishing gives no implication.
  waldhausen-free-double-whitehead-space-contractible: that node concerns free-group doubles, whereas this is Waldhausen's separate one-relator membership theorem for his class Cl.
---

If `G` is a torsion-free one-relator group and `H<=G` is any subgroup, with
no finiteness hypothesis on `H`, then

```text
Wh(H) = 0.
```

Equivalently, the degree-one integral algebraic K-theory assembly map for
`H` is surjective. In fact Waldhausen's theorem makes the entire Whitehead
space `Wh_Z(H)` contractible. Taking `H=G` gives the one-relator case itself.

**ESTABLISHED 2026-08-30** by
[[whitehead-one-relator-via-waldhausen-class-cl]].
