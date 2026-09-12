---
rg: 2
id: affine-disjoint-tag-packing-proof
kind: route
title: Count disjoint affine images of the dummy-character fiber
target: affine-source-charts-have-a-disjoint-tag-packing-ceiling
requires: []
---

Every character of `H=D times E` is a pair in `D^hat times E^hat`.  Fixing
the original source character and leaving the dummy factor unconstrained
gives exactly the fiber `(ASP1)`.  An automorphism of `H` acts invertibly and
affinely on the character vector space, so it preserves the cardinality
`2^t` of that fiber.  Pairwise disjoint images of `L` fibers occupy
`L 2^t` points inside the `2^(r+t)`-point target dual.  This is `(ASP2)`.

For canonical microstates of a fixed finite subgroup, flexible
exactification and trace convergence give asymptotically equal multiplicity
to every regular character.  Hence a construction retaining `1-o(1)` of the
source atom must retain `1-o(1)` of every fiber's total character mass, and
the same counting inequality survives with an `o(1)` error.
