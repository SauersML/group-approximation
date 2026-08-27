---
rg: 2
id: cz-spectral-cut-carrier-holonomy-audit-proof
kind: route
title: Resolve the multiplicity involution and pull the selected cut through the Whitehead leaf
target: spectral-cut-removes-cz-orientation-but-not-carrier-holonomy
requires:
  - controlled-fine-reflection-superrank-orientation-law
  - literal-prefix-three-root-swap-retains-typed-carriers
---

The Schur form `T=C tensor V` gives the complementary spectral projections
`G_+,G_-`.  Restriction to either nonzero eigenspace makes `T` equal to `C`
or `-C`; multiplication by the marked central sign corrects the latter.

For the boundary, use the exact typed countermodel with a common leaf `K`,
a two-leaf source completion and a four-leaf target completion.  Choose any
involution on `K`, resolve it into `G_+,G_-`, and let the partial swap carry
the selected leaf cut unitarily.  Its source and target packet completions
still have ranks `2 rank(G)` and `4 rank(G)`.  All local orientation and leaf
transport statements hold, while the two carrier identities remain
different.  This proves both the positive spectral-selection assertion and
the claimed holonomy firewall.

