---
rg: 2
id: property-t-free-leavitt-via-corona-module-decoder
kind: route
title: Decode a surviving root and apply corona Hilbert-hotel cancellation
target: property-t-free-leavitt-full-mf-radical
requires:
  - corona-coefficient-module-decoder
  - finite-root-heisenberg-multiplicity-germs
  - corona-projective-hilbert-hotel-cancellation
---

Assume a norm-corona representation keeps the specified root nontrivial.
The finite root and Heisenberg windows supply the compatible exact
multiplicity germs consumed by the coefficient-module decoder.  The decoder
produces a nonzero finitely generated projective matrix-corona module with a
unital action of the binary Leavitt family.

That action gives an isomorphism `P ~= P + P`.  Exact rank-germ cancellation
forces `P=0`, a contradiction.  Thus every norm-corona representation kills
the specified root.  Since the root normally generates `E_n(R)`, every such
representation is trivial and the whole group is its MF radical.
