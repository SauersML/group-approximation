---
rg: 2
id: terminated-digit-boundary-refinement-transport-proof
kind: route
title: Match digit tiles modulo h minus one and match their clopen complements by graph expansions
target: terminated-digit-boundary-sets-have-prefix-transport
requires:
  - terminated-digit-carries-form-finite-injection-nucleus
artifacts:
  - research/artifacts/boone-higman-enlarged-digit-fiber-stabilizer-2026-09-08.md
---

A tile alpha*T splits into its h digit children. This replaces
one tile by h tiles and leaves its count unchanged modulo h-1.
Two tiles intersect only when their prefixes are comparable and
the intervening path uses only digit loops. In that case one is
contained in the other. Matching finitely many prefixes gives a
common refinement of any two finite tile partitions of the same
set. It also expresses intersections and differences as finite
tile unions. This proves well-definedness and the Boolean claims.

For g in H_(h,r), subdivide a tile into sufficiently long digit
prefixes that every corresponding local action belongs to the
four-map nucleus. These domains terminate at Y, so the possible
states are id_Y,I,D. Their restrictions to T are

    id_T,       a,       prefix(h)*a^-1,

where a is the h-adic adding machine on digits 1,...,h. The last
identity follows from D*I(z)=h*z and I(T)=T. Each state therefore
maps one boundary tile onto one boundary tile. Splitting the source
changes its count only by multiples of h-1; the images are disjoint
by injectivity. Thus g preserves both boundary sets and b.

## A clopen complement calculation

A finite graph-prefix forest for a nonempty clopen set has x leaves
of type X and y leaves of type Y. Its weight is r*x+y modulo
n=r+h-1. Expanding an X leaf replaces it with r Y leaves and
preserves the weight exactly. Expanding a Y leaf adds one X leaf
and h-1 Y leaves, increasing the weight by n.

Expand all X leaves to obtain only Y leaves. From a Y-only forest,
expand one Y leaf and then its new X child; this adds exactly n Y
leaves. Consequently two nonempty forests with the same weight
modulo n can be expanded to identical numbers of Y leaves. Matching
those leaves gives a canonical prefix bijection of their clopen sets.

## Supported transport

Let A,A' be as in the claim. First refine their tiles until the
associated Y cones are pairwise disjoint, lie inside D, and their
unions U,U' are proper subsets of D. These refinements are possible
by compactness: every tile is closed and nowhere dense, and a
finite family of disjoint compact tiles has disjoint clopen
neighborhoods of this prefix form. Further digit refinements remain
inside those neighborhoods.

Since b(A)=b(A'), refine more until the tile counts are equal,
say q. Match the q Y cones by canonical prefix maps, sending A
exactly to A'. The nonempty complements D minus U and D minus U'
have the same weight modulo n: each has weight weight(D)-q.
The preceding forest calculation supplies a prefix bijection
between these complements. Glue the two bijections and extend
by the identity off D. This is the asserted supported prefix
homeomorphism, whose recurrent local actions are identities.

If A and A' are disjoint from F, their compact union lies in
C_X minus F. This open set is the disjoint union of the first-gap
token cones token(j)*C_X. Finitely many of those cones cover
A union A'; their union is a valid D disjoint from F.
