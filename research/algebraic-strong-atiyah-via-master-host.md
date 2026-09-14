---
rg: 2
id: algebraic-strong-atiyah-via-master-host
kind: route
title: Test Strong Atiyah and the determinant conjecture at the master host
target: algebraic-strong-atiyah-for-all-torsion-free-groups
requires:
  - algebraic-atiyah-and-determinant-one-group-tester
  - master-host-satisfies-algebraic-strong-atiyah
  - master-host-satisfies-determinant-conjecture
---

If `E` satisfies Strong Atiyah over `Qbar` and the determinant conjecture,
then by [[algebraic-atiyah-and-determinant-one-group-tester]] every
torsion-free group satisfies both, in particular Strong Atiyah over `Qbar`.

This is a genuine reduction and not a restatement: the prerequisites also
assert the determinant conjecture for every torsion-free group, which the
target does not.
