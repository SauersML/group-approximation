---
rg: 2
id: lamplighter-fp-amenable-interface-directional-proof
kind: route
title: Combine the Baumslag--Remeslennikov embedding with the Bieri--Strebel cover theorem
target: lamplighter-fp-amenable-interface-is-directional
requires: []
---

Benli--Grigorchuk--de la Harpe, Remark A.4(c), records that the finitely
presented group

```text
<a,s,t | a^t=a a^s, [s,t]=1, [a,a^s]=1>
```

is metabelian and contains `Z wr Z`.  Metabelian groups are amenable, so
this gives the required finitely presented amenable overgroup.

The same paper's Theorem 1.5, via Bieri--Strebel, says that every finitely
presented cover of a finitely generated, infinitely presented, virtually
metabelian group contains a nonabelian free subgroup.  The lamplighter
`Z wr Z` satisfies those hypotheses.  Therefore every finitely presented
`E` with `E ->> Z wr Z` contains `F_2` and is nonamenable.  A
retraction from an amenable finitely presented overgroup would make that
overgroup such a cover, so no such retraction exists.
