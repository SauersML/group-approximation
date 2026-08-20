---
rg: 2
id: nonhyperlinear-from-uniform-finite-bi-index-clifford-tape
kind: route
title: Round one infinite coset lamp family and apply compact Pauli packing
target: non-hyperlinear-group
requires:
  - finite-bi-index-clifford-tape-presentation
  - uniform-hs-site-coherence-for-finite-bi-index-pair
  - uniform-infinite-pauli-packing-impossible
---

Use the pair supplied by the coherence claim in `(FCT1)`.  The presentation
claim gives a finitely presented group with `J!=1`.  If this group were
hyperlinear, sufficiently accurate microstates would keep `J` at its
canonical positive separation.  The coherence theorem then produces, on a
nonzero finite-dimensional marked carrier, one unitary `A_x` for every coset
`x in L/H`, with the uniform bound `(FSC1)`.

Choose the microstate defect so small that the right side of `(FSC1)` is less
than `2`.  Since `L/H` is infinite,
`uniform-infinite-pauli-packing-impossible` gives a contradiction.  Therefore
the presented group is not hyperlinear.

