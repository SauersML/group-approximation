---
rg: 2
id: strict-design-with-one-relator-table-group
kind: claim
title: Some strict automaton design has a one-relator canonical table group
distinct_from:
  triangular-forward-tables-force-surjectivity: that proves designs whose forward partitions eliminate completely are bijective; this asks for a strict design whose forward partition leaves exactly one relator after elimination.
  nonsofic-one-relator-group: that asks for a nonsofic one-relator group directly; this asks for one arising as the table group of a strict automaton design, which would supply it.
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
---

**OPEN.** Exhibit a design `(A, S, M, nu, mu)` and a minimal forward-sufficient
marked partition `E` whose canonical table group `U_E`, after the triangular
eliminations of `triangular-forward-tables-force-surjectivity`, is a one-relator
group, and over which the realization is injective and not surjective.

## Attempts

- *Two relators are needed before elimination.* Every forward partition with at
  most one relator is triangular, so its table group is free and the automaton is
  bijective. A strict design needs a core that survives elimination. This claim
  asks for the smallest possible core.
- *What the core would have to be.* A strict realization over `U_E` makes `U_E`
  nonsofic (Gromov--Weiss, as recovered in
  `sofic-radical-localizes-garden-of-eden-windows`). So the core would be a
  witness for `nonsofic-one-relator-group`, and it inherits every constraint
  recorded there: torsion-free, two-generator after reduction, primitivity rank
  two, no nontrivial finitely generated Kazhdan subgroup. The last one is the
  decisive gap. The only known nonsoficity mechanism uses Kazhdan subgroups, so a
  one-relator core cannot carry it. This is where the attempt dies: the
  prerequisite is at least as hard as that root, and no candidate is known.
