---
rg: 2
id: amenable-cd-two-coherence-via-aspherical-presentations
kind: route
title: Aspherical presentations with finitely many generators force finite presentation for amenable cd-2 groups, hence solvability, hence coherence of the rational group algebra
target: amenable-cd-two-rational-group-algebras-are-coherent
requires:
  - amenable-cd-two-groups-have-aspherical-presentations
  - amenable-free-top-syzygy-forces-type-fp
  - amenable-cd-two-solvable-iff-coherent-rational-group-algebra
---

Let `G` be amenable with `cd G = 2`. Every finitely generated subgroup `H` of `G` has `cd H <= 2`.
If `cd H = 2`, `amenable-cd-two-groups-have-aspherical-presentations` gives `H` a free second
syzygy for some finite generating set. Item 3(c) of `amenable-free-top-syzygy-forces-type-fp` then
makes `H ≅ BS(1,m)`. If `cd H <= 1`, then `H` is free and amenable, hence cyclic. So every finitely
generated subgroup of `G` is metabelian, and `G` is metabelian, in particular solvable.
`amenable-cd-two-solvable-iff-coherent-rational-group-algebra` then gives left coherence of
`Q[G]`.

The converse holds as well (item 3(c) of `amenable-free-top-syzygy-forces-type-fp`), so this route
is a strict reduction with both directions.
