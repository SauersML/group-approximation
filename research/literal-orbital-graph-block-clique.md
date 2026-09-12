---
rg: 2
id: literal-orbital-graph-block-clique
kind: claim
title: Each block of the literal orbital graph is a complete subgraph
distinct_from:
  literal-lamp-kernel-clifford-block-amalgam: that is the full kernel decomposition; this is its graph-theoretic block input.
  literal-telescope-split-normal-form: that identifies the vertical quotient; this identifies adjacency on sites.
artifacts: [notes/LITERAL_ORBITAL_CLIQUE_ROUTE.md, GroupApproximation/Sofic/LiteralBlockGeometry.lean, GroupApproximation/Sofic/LiteralAffineCosetTransitivity.lean]
---

In the literal orbital graph, two distinct sites are adjacent exactly when
they lie in the same block.  Forward adjacency preserves the equivariant
block label; conversely the explicit affine-coset transitivity moves the
marked pair to every distinct pair in a block.  The theorem is formalized on
both carriers.  The separate telescope/carrier wiring issue does not affect
this graph statement.
