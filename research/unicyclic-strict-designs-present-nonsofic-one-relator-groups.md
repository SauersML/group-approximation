---
rg: 2
id: unicyclic-strict-designs-present-nonsofic-one-relator-groups
kind: claim
title: A strict design whose connected difference graph has one independent cycle presents a nonsofic one-relator group
distinct_from:
  nonsofic-one-relator-group: that asks for a nonsofic one-relator group by any means; this shows one specific kind of Gottschalk counterexample would supply one, so a positive answer to Pestov 4.10 forces every strict design to carry two independent coincidence cycles.
  triangular-forward-tables-force-surjectivity: that excludes forward partitions whose relators peel one letter at a time, where the table group is free; this concerns partitions with one independent cycle, where the table group is a one-relator group that need not be free.
artifacts:
  - research/artifacts/table-group-holonomy-normal-form-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `unicyclic-strict-design-one-relator-proof`.

Let `D` be a design and `E` a forward-sufficient partition whose decoder difference
graph is connected and has first Betti number at most one. Then the table group
`U_E` is free or a one-relator group on the memory letters
(`table-groups-are-memory-holonomy-groups`). If the realization over `U_E` is strict,
then `U_E` is a one-relator group that is not sofic.

By the reduction to connected minimal designs, every counterexample to Gottschalk's
conjecture falls into one of two cases:
- it yields a nonsofic one-relator group, a negative answer to Pestov's Question
  4.10 (`one-relator-groups-sofic`);
- it has a connected minimal design with at least two independent coincidence
  cycles.

By `nonsofic-one-relator-relator-has-primitivity-rank-two`, the holonomy of the
unique cycle of such a strict design is not a proper power, and the group it
presents is torsion-free and locally indicable.
