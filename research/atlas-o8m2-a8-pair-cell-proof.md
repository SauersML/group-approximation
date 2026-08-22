---
rg: 2
id: atlas-o8m2-a8-pair-cell-proof
kind: route
title: Compute the five degree-1632 point-stabilizer orbits and Sp6 incidences
target: atlas-o8m2-a8-pairs-have-five-normalizer-cells
requires:
  - atlas-o8m2-has-one-a8-class-with-c3-centralizer
  - atlas-a4-sp6-packet-collision-screen
artifacts:
  - experiments/atlas_o8m2_a8_pair_cells.py
  - experiments/atlas-o8m2-a8-pair-cells.json
---

The replay constructs `PrimitiveGroup(1632,1)` and its point stabilizer `N`.
For each `N`-orbit representative `1^g`, it computes `N intersect N^g`,
`A intersect A^g`, and `<A,A^g>` exactly.  It independently enumerates the
136 conjugates of the unique maximal `Sp6(2)` and finds the three containing
the fixed `A`.  Counting which of these also contains `A^g` gives the last
column of `(OMP1)`.  Assertions pin the orbit sum `1632` and the already
established `136*36=1632*3` incidence.

