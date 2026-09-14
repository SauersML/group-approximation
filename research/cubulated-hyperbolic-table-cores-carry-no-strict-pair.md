---
rg: 2
id: cubulated-hyperbolic-table-cores-carry-no-strict-pair
kind: claim
title: A forward table whose two-core presents a hyperbolic cubulated group carries no strict pair
distinct_from:
  forward-relations-of-a-counterexample-have-a-nonsofic-core: that proves the two-core of a counterexample presents a nonsofic group; this certifies soficity syntactically for cores that are hyperbolic and cubulated, such as finite classical C'(1/6) cores.
  cprime-one-sixth-presentations-are-hyperlinear: that concerns hyperlinearity of a presentation; this is a design filter on forward tables of automata.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

**ESTABLISHED** by `cubulated-hyperbolic-table-core-filter-proof`.

Let `T_f` be a forward table, and `C(D)` the group presented by the 2-core of its
relator hypergraph. If `C(D)` is hyperbolic and acts properly cocompactly on a CAT(0)
cube complex (for example, if the core presentation is finite classical `C'(1/6)`),
then no strict data with forward table `T_f` is realized in any group, for any alphabet
and any rules.

So every counterexample's core has flats (Section 3 of the artifact, lattices in
products of trees) or non-cubulated geometry, such as Kazhdan cores.
