---
rg: 2
id: amenable-cd-two-coherence-via-l2-rank-gap
kind: route
title: An L2-rank gap for every finitely generated amenable cd-2 group makes each such group BS(1,m), so every amenable cd-2 group is metabelian and its rational group algebra is coherent
target: amenable-cd-two-rational-group-algebras-are-coherent
requires:
  - amenable-cd-two-groups-have-an-l2-rank-gap
  - amenable-cd-two-l2-rank-gap-forces-baumslag-solitar
  - amenable-cd-two-solvable-iff-coherent-rational-group-algebra
---

Let `G` be amenable with `cd G = 2`. Let `H ≤ G` be finitely generated. Then `H` is amenable with
`cd H <= 2`.

- If `cd H = 2`, `amenable-cd-two-groups-have-an-l2-rank-gap` gives `H` an `L²`-rank gap. Item 3
  of `amenable-cd-two-l2-rank-gap-forces-baumslag-solitar` then gives `H ≅ BS(1,m)`.
- If `cd H = 1`, `H` is free (Stallings–Swan) and amenable, hence `Z`.
- If `cd H = 0`, `H = 1`.

So every finitely generated subgroup of `G` is metabelian. Each identity
`[[a,b],[c,e]] = 1` involves four elements, which lie in a finitely generated subgroup. So `G` is
metabelian, hence solvable. `amenable-cd-two-solvable-iff-coherent-rational-group-algebra`
((1) ⇒ (2)) gives left coherence of `Q[G]`.

**Converse.** The target implies the gap, by item 4 of
`amenable-cd-two-l2-rank-gap-forces-baumslag-solitar`. That item goes through
`amenable-cd-two-solvable-iff-coherent-rational-group-algebra` and Linnell's theorem. So this route
is a strict reduction with both directions. The converse is not recorded as a route, which keeps
the graph acyclic.
