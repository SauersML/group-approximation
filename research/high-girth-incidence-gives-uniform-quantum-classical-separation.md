---
rg: 2
id: high-girth-incidence-gives-uniform-quantum-classical-separation
kind: claim
title: High-girth graph incidence systems separate operator and classical solvability for every modulus
distinct_from:
  slofstra-zhang-high-girth-phase-survival: that is the general hypergraph phase-order theorem; this specializes it to oriented graph incidence and combines it with the elementary classical obstruction.
  mipstar-bcs-tracial-nonru-exists: that supplies a tracial system with no Connes-embeddable model; these incidence systems are only known here to have possibly infinite-dimensional operator solutions.
---

Let `G` be a connected graph with minimum degree and girth at least `(4,4)`
or `(3,6)`.  Orient its edges arbitrarily and let `I(G)` be the signed
vertex-edge incidence matrix.  For every integer `p>=2` and every vertex
weight vector `b`:

1. `I(G)x=b` has a classical solution over `Z_p` exactly when
   `sum_v b_v=0` in `Z_p`;
2. `I(G)x=b` has a possibly infinite-dimensional operator solution for every
   `b`; and therefore
3. whenever `sum_v b_v!=0`, the associated linear-system game has a perfect
   commuting-operator strategy but no perfect classical strategy.

For item 1, summing the vertex equations annihilates every oriented edge
column.  Connectedness gives the converse by solving along a spanning tree.
For item 2, all nonzero incidence coefficients are `+1` or `-1`, hence are
non-zero-divisors modulo every `p`.  The Slofstra--Zhang high-girth theorem
gives `order(J)=p`, and
`solution-group-central-order-is-operator-solvability` converts that order
into an operator solution.

The construction is uniform in the right-hand side and works for odd `p`,
where it supplies exact quantum/classical separation beyond generalized
Pauli models.  It does **not** establish a finite-dimensional operator
solution; Slofstra--Zhang explicitly leave that question open for these
odd-modulus examples.
