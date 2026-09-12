---
rg: 2
id: universal-torsion-free-subgroup-colimit-class-tester-proof
kind: route
title: Embed the recursive stages and then take their arbitrary colimit
target: universal-torsion-free-subgroup-colimit-class-tester
requires: [whitehead-universal-finitely-presented-torsion-free-group, torsion-free-directed-colimit-recursively-presented]
---

Fix the finitely presented torsion-free group `U` from
[[whitehead-universal-finitely-presented-torsion-free-group]]. Only its
group-theoretic universality is used: every countably generated recursively
presented torsion-free group embeds in `U`.

Let `C` have the two permanence properties in the claim and assume
`U in C`. For an arbitrary torsion-free group `G`,
[[torsion-free-directed-colimit-recursively-presented]] supplies

```text
G=colim_i K_i,
```

where every `K_i` is finitely generated, recursively presented, and
torsion-free, while the structure maps may be noninjective. Every `K_i`
embeds in `U`, hence lies in `C` by subgroup closure. Arbitrary
directed-colimit closure then gives `G in C`.

Conversely, if every torsion-free group lies in `C`, then `U in C`
because `U` is torsion-free. The argument did not depend on `C`, so the
same fixed group works simultaneously for all such classes. QED

The phrase “arbitrary structure maps” is essential: the torsion-free
reflection system used in the decomposition need not have injective maps.
