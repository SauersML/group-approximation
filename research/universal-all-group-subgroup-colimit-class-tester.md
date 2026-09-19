---
rg: 2
id: universal-all-group-subgroup-colimit-class-tester
kind: claim
title: One two-generator finitely presented group tests every subgroup-and-colimit closed property on all groups
distinct_from:
  universal-torsion-free-subgroup-colimit-class-tester: that uses the torsion-free universal host and a torsion-free reflection system; this is the unrestricted all-group theorem and its host necessarily has torsion.
  universal-local-approximation-fixed-two-generator-test-group: that treats finite-table approximation properties through marked closure; this applies to every class having the two stated categorical permanence properties.
  classical-bass-fixed-two-generator-testers: that proves conjugacy-sensitive Bass inheritance using Frattini embeddings; this abstract theorem assumes ordinary subgroup inheritance from the outset.
---

There exists a fixed two-generator finitely presented group `U` with the
following simultaneous property. For every class of groups `C` which is

1. closed under taking subgroups, and
2. closed under directed colimits with arbitrary, not necessarily injective,
   structure maps,

one has

~~~text
U belongs to C
  <=>
every group belongs to C.
~~~

The same `U` works for every such class. It may be chosen as the all-group
host in [[whitehead-universal-finitely-presented-container]], hence also as
the host in [[two-generator-frattini-universal-containers]], and satisfies

~~~text
Tord(U)={2,3,4,...}.
~~~

**ESTABLISHED 2026-08-31** by
[[universal-all-group-class-tester-proof]].
