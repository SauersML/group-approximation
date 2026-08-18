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
suffices for a sofic model.  The point is to make GSD-2 a genuine near-perfect
nibble/packing question, with the hard `l=m` local reservoir now supplied
explicitly, rather than an absorption theorem burdened by unnecessary exact
completion.
