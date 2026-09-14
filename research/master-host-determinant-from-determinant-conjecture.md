---
rg: 2
id: master-host-determinant-from-determinant-conjecture
kind: route
title: Restrict the universal determinant conjecture to the master host
target: master-host-satisfies-determinant-conjecture
requires:
  - determinant-conjecture
---

If every group satisfies Lueck's determinant conjecture
([[determinant-conjecture]]), then in particular the two-generator torsion-free
master tester `E` does.  No permanence is needed; this is specialization.

The converse holds only in the torsion-free lane: by item 6 of
`two-generator-fp-torsion-free-master-tester` and the colimit permanence of
the determinant conjecture, `Det(E)` gives the conjecture for every
torsion-free group, not for groups with torsion.
