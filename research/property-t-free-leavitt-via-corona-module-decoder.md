---
rg: 2
id: property-t-free-leavitt-via-corona-module-decoder
kind: route
title: Decode a surviving root and apply corona Hilbert-hotel cancellation
target: property-t-free-leavitt-full-mf-radical
requires:
  - corona-coefficient-module-decoder
  - finite-root-heisenberg-multiplicity-germs
  - finite-root-windows-share-one-reducing-corona-carrier
  - binary-leavitt-two-branch-character-restriction-is-faithful
  - corona-projective-hilbert-hotel-cancellation
  - torsion-normal-generator-has-full-support-corona-core
  - torsion-active-core-is-a-uniform-morita-generator
---

Assume a norm-corona representation keeps the specified finite-order root
nontrivial.  Full-support reblocking first replaces the model by a stably
equivalent active-core model in which the root spectral projection has a
uniform positive rank fraction.  The finite root and Heisenberg windows then
supply the compatible exact multiplicity germs consumed by the
coefficient-module decoder.  The decoder produces a nonzero finitely
generated projective matrix-corona module with a unital action of the binary
Leavitt family.

The reducing sparse-character theorem places every finite packet and both
branch actors in one literal nonzero corner.  The two branch character labels
jointly determine the global label.  Thus no stabilization size or carrier
is allowed to vary with the packet window; the only new construction
performed by the decoder is the coherent choice of coefficient intertwiners
and their products.

That action gives an isomorphism `P ~= P + P`.  Exact rank-germ cancellation
forces `P=0`, a contradiction.  Thus every norm-corona representation kills
the specified root.  Since the root normally generates `E_n(R)`, every such
representation is trivial and the whole group is its MF radical.
