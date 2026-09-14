---
rg: 2
id: strict-automata-live-on-canonical-table-groups-proof
kind: route
title: Read both composites off the product tables, coarsen, and pull back along the table-group homomorphism
target: strict-automata-live-on-canonical-table-groups
requires: []
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
---

Complete direct proof, Sections 1 to 3 of the artifact.

- Both composites read symbols on product classes, so their identities are properties
  of the two marked partitions. Coarsening preserves them.
- Injective automata have finite-memory left inverses by compactness.
- Given a strict realization, pick a minimal forward-sufficient partition below its
  forward table. The table group of that partition maps to the realization's group
  by `x_a -> rho(a)`. That map coarsens the reverse table, so a reverse-sufficient
  table upstairs would force surjectivity downstairs.
- Over a sofic quotient the realization is injective, hence surjective by
  Gromov--Weiss. Its reverse table dominates a minimal reverse hinge, whose words
  therefore all die.
