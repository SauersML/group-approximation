---
rg: 2
id: regular-table-local-h1-gives-spherical-gauge
kind: route
title: Apply short-edge H1 triviality to regular-table relation defects
target: spherical-short-holonomies-admit-local-gauge
requires:
  - spherical-relation-defect-pairs-small-chord
  - relation-defects-obey-permutation-gauge-law
  - regular-table-defects-are-short-edge-h1-trivial
  - short-edge-gauge-torsor-h1-vanishes
---

After charging the matching-completion and unitary-bad roots,
`spherical-relation-defect-pairs-small-chord` places every relation defect in
the short-edge coefficient system.  The permutation gauge law identifies the
simultaneous correction equations with the corresponding nonabelian torsor.

The new prerequisite
`regular-table-defects-are-short-edge-h1-trivial` supplies the point omitted
by the previous route: the defect class is trivial inside the local
coefficient system, rather than only after inclusion into the full symmetric
group.  The conditional theorem
`short-edge-gauge-torsor-h1-vanishes` then gives source corrections of radius
`O_T(rho)` outside `O_T(eta)` roots.  Sending the matching tolerance and
exceptional density to zero gives all three clauses of
`spherical-short-holonomies-admit-local-gauge`.

No inference from ambient compatibility to local triviality is used.
