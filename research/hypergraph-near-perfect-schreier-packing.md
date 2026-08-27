---
rg: 2
id: hypergraph-near-perfect-schreier-packing
kind: claim
title: The spherical local-reservoir package admits a coupled near-perfect Schreier packing
---

Given the finite coloured candidate system supplied by
`spherical-near-perfect-local-package`, find partial bijections for the tested
generators whose domains and ranges omit only `o(N)` vertices, such that every
tested multiplication/relator constraint holds on `1-o(1)` of the roots and
every tested nontrivial word moves `1-o(1)` of the roots.

This is deliberately weaker than `hypergraph-absorption-schreier-matching`:
perfect matchings and exact divisibility are not requested.  By
`partial-schreier-completion-preserves-sofic-loss`, this weaker packing already
suffices for a sofic model.

The acyclic part of the problem is now closed.  `spherical-single-relation-near-perfect-packing`
solves one relation, and `spherical-one-shared-map-relation-extension` shows
that every relation which meets the previously chosen system in only one
label can be attached by a tight matching plus exact composition.  Hence
`spherical-one-overlap-forest-rounding` proves the whole claim for every
one-overlap relation forest.

The remaining content is therefore **cycle synchronization**: close a
relation which reuses at least two label maps already constrained by earlier
relations, without changing those maps on more than `o(N)` vertices.  Any
nibble/weight-preservation theorem used here must control agreement of these
shared permutation copies, not merely preserve marginal candidate degrees.
