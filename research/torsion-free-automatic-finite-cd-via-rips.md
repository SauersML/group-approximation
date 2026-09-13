---
rg: 2
id: torsion-free-automatic-finite-cd-via-rips
kind: route
title: Contractible Rips complexes of automatic groups would give finite cohomological dimension in the torsion-free case
target: torsion-free-automatic-groups-have-finite-cd
requires:
  - automatic-groups-have-contractible-rips-complexes
  - torsion-free-contractible-rips-complex-gives-type-f
---

Let `G` be torsion-free and automatic. By
`automatic-groups-have-contractible-rips-complexes` some Rips complex
`P_d(G, S)` is contractible. By
`torsion-free-contractible-rips-complex-gives-type-f`, a torsion-free group with
a contractible Rips complex has a finite classifying space of dimension at most
`|B_S(1, d)| - 1`. In particular `cd G < ∞`.

This is a genuine reduction, not a restatement. The prerequisite asks for a
specific contractible complex for every automatic group, with or without
torsion. The target asks only for a dimension bound in the torsion-free case.
