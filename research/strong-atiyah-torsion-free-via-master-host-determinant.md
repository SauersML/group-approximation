---
rg: 2
id: strong-atiyah-torsion-free-via-master-host-determinant
kind: route
title: Prove Strong Atiyah over Qbar and the determinant conjecture at the master host, then change base under the determinant conjecture
target: strong-atiyah-torsion-free
requires:
  - algebraic-atiyah-and-determinant-one-group-tester
  - master-host-satisfies-algebraic-strong-atiyah
  - master-host-satisfies-determinant-conjecture
  - determinant-conjecture-gives-full-atiyah-base-change
---

* **Transport from the host.** Assume `SA(E)` and `Det(E)` for the two-generator
  torsion-free master tester `E`
  ([[master-host-satisfies-algebraic-strong-atiyah]],
  [[master-host-satisfies-determinant-conjecture]]). By
  [[algebraic-atiyah-and-determinant-one-group-tester]], every torsion-free group
  `G` then satisfies Strong Atiyah over `Qbar` and the determinant conjecture.
* **Base change.** [[determinant-conjecture-gives-full-atiyah-base-change]] turns
  those two properties of `G` into Strong Atiyah over `C` for `G`. This covers
  every subfield `K` of `C` in the root.

**Not a restatement.** The prerequisites assert the determinant conjecture for
every torsion-free group, which the root does not. The route replaces the
Galois-invariance hypothesis of `strong-atiyah-torsion-free-via-algebraic-base-change`
by the determinant conjecture.

**Status of the base-change input.** Proved for coefficient fields of
transcendence degree at most one
(`atiyah-base-change-in-transcendence-degree-one-under-det`). Open from
transcendence degree two.
