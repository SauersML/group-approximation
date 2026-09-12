---
rg: 2
id: cantor-prefix-clopen-centralizer-reconstruction-proof
kind: route
title: Recover clopen images from finite centralizer tests between localized copies of V
target: cantor-prefix-markings-compute-clopen-action
requires:
  - cantor-punctured-prefix-groups-detect-word-problem
artifacts:
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
---

For a clopen U let V_U consist of prefix homeomorphisms supported
in U. When U is nonempty, a finite prefix bijection from C onto U
conjugates V to V_U. Thus V_U has an effective finite generating
set of prefix tables. Express these tables in the marked generators
of V by enumeration and exact prefix-table comparison. This search
terminates because the tables belong to V. For U empty, use the
empty generating set.

The required discriminator claim with F empty supplies a word-problem
algorithm for D from its recursive presentation and any fixed
nonidentity marked element of V.

## The inclusion test

For any clopen U,W and homeomorphism g in D,

    g(U) subset W  iff  [g V_U g^-1, V_(C minus W)] = 1.

Disjoint supports prove the forward implication. Conversely, a
homeomorphism centralizing V_O fixes O pointwise: if it moves a
point of O, choose a sufficiently small cone B in O disjoint from
its image. A nonidentity prefix map supported in B cannot equal
its conjugate, whose support is disjoint. Apply this with
O=C minus W to each element of g V_U g^-1. If g(U) meets O,
that intersection is open and the conjugated localized group has
an element moving a point there, a contradiction.

Two finitely generated subgroups commute exactly when every pair
of chosen generators commutes. Consequently the displayed inclusion
is decided by finitely many word-problem tests in D.

## Exact reconstruction and uniqueness

Enumerate all finite prefix codes representing clopen sets W. Test
both g(U) subset W and g^-1(W) subset U by the inclusion criterion.
The two tests together say g(U)=W. Such a W exists because g is a
homeomorphism, so the search terminates. Empty and whole clopen
sets are included in the enumeration.

To compute an output prefix of g(x), compute the preimages of the
finitely many cylinders of that output length. They are a clopen
partition represented by finite prefix codes. Finitely many bits
of x identify its member, and hence the required output prefix.
The same procedure works for g^-1.

For uniqueness, the truth of every commutator equation used in the
inclusion criterion is determined by the abstract marked group.
Two faithful actions extending the same V marking therefore have
identical g(U) for every g and clopen U. Clopen sets separate points,
so the actions agree. This argument uses neither recursive
presentability nor a word-problem algorithm. Faithfulness makes
commutation of acting elements equivalent to equations in D.

Finally, given computable p and a finite marking for D_p, run two
searches on a word g. Enumerate words in the stabilizer generators
and compare them to g using the word-problem algorithm. In parallel,
compute increasingly long prefixes of g(p) and p until they differ.
Exactly one search succeeds. Thus membership in D_p is decidable.
Finite generation here is an extra hypothesis, not a consequence
of computability of the Cantor action.
