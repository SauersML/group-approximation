---
rg: 2
id: finite-overgroup-packing-preserves-hyperlinearity-proof
kind: route
title: Apply amenable-edge permanence to the finite packet graph
target: finite-overgroup-packing-preserves-hyperlinearity
requires:
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
  - canonical-types-extend-every-finite-bass-serre-actor
---

Every finite group is hyperlinear and amenable.  Hence `(FOC1)` is a finite
graph of hyperlinear vertex groups with amenable edge groups.
`amenable-edge-graph-corners-cannot-groupify-a-nonce-game` gives
hyperlinearity of its fundamental group whenever `Gamma` is hyperlinear.

The representation-level statement is
`canonical-types-extend-every-finite-bass-serre-actor`.  A canonical
matrix-ultraproduct embedding of `Gamma` restricts to the normalized regular
trace on every `H_i`.  Embed each `G_i` by its normalized regular trace.  The
two embeddings of `C[H_i]` are trace preserving and hence unitarily conjugate
inside the matrix-ultraproduct factor.  After this conjugacy they agree, so
the universal property gives an embedding of the amalgam.  Non-tree edges
are handled by independent conjugating unitaries in the same way.

Therefore finite character packing may provide projection identities inside
the extension, but it cannot destroy a canonical matrix model that existed
for the base.  This proves the claim.
