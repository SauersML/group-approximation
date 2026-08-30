---
rg: 2
id: universal-torsion-free-subgroup-colimit-class-tester
kind: claim
title: One finitely presented torsion-free group tests every subgroup-and-colimit closed property
distinct_from:
  whitehead-universal-finitely-presented-torsion-free-group: that tests Whitehead vanishing using injectivity on a particular functor; this is a property-independent universal theorem using only subgroup and arbitrary directed-colimit closure.
  full-farrell-jones-fixed-fp-torsion-free-tester: that is the Full Farrell--Jones instance; this is the abstract closure principle which applies to any class with the two stated permanence properties.
  torsion-free-directed-colimit-recursively-presented: that decomposes one arbitrary torsion-free group; this adds the fixed universal host and quantifies over all suitable classes.
---

There exists a fixed finitely presented torsion-free group `U` with the
following simultaneous property.

For every class of groups `C` which is

1. closed under taking subgroups, and
2. closed under directed colimits with arbitrary structure maps,

one has

```text
U belongs to C
  <=>
every torsion-free group belongs to C.
```

The same `U` works for every such class `C`; it may be chosen as the
witness in
[[whitehead-universal-finitely-presented-torsion-free-group]].

**ESTABLISHED 2026-08-30** by
[[universal-torsion-free-subgroup-colimit-class-tester-proof]].
