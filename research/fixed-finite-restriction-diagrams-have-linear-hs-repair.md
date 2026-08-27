---
rg: 2
id: fixed-finite-restriction-diagrams-have-linear-hs-repair
kind: claim
title: Every fixed finite restriction diagram has multiplicity-independent linear HS repair
distinct_from:
  finite-group-multiplicity-mismatch-pays-hs-energy: that lower-bounds intertwining energy from a supplied mismatch for two representations of one finite group; this also rounds the two vertex multiplicity vectors into the exact equal-restriction monoid and constructs repaired vertex representations.
  finite-group-shared-overlap-polar-alignment: that extracts a large common edge submodule but need not make its supports reduce the two larger vertex groups; this uses the fixed branching matrices to alter whole vertex blocks and then obtains a full unitary edge intertwiner.
  iwahori-fractional-transport-integralization: that asks for a uniform theorem over unbounded Iwahori types; this proves the integralization and repair when the entire quotient diagram is fixed and finite.
---

Fix finite groups `G_1,G_2`, a finitely generated group `B`, homomorphisms
`phi_i:B->G_i`, and a finite generating set `S_B`.  There is a constant
`C_D`, depending only on this finite diagram, such that the following holds
in every dimension `d`.

For exact representations `pi_i:G_i->U(d)`, put

```text
epsilon=max_(s in S_B)
  ||pi_1(phi_1(s))-pi_2(phi_2(s))||_2.                 (FDR1)
```

There are exact representations `pi~_i:G_i->U(d)` satisfying

```text
pi~_1(phi_1(b))=pi~_2(phi_2(b))             (b in B), (FDR2)
max_(g in G_i)||pi_i(g)-pi~_i(g)||_2<=C_D epsilon.     (FDR3)
```

The same statement holds for any finite family of diagrams after taking the
maximum of their constants.  No irreducible degree or isotypic multiplicity
appears in the bound.

