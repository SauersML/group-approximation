---
rg: 2
id: iwahori-fractional-transport-integralization-via-clusters
kind: route
title: Upgrade low-gap cluster unitaries by atomizing each component
target: iwahori-fractional-transport-integralization
requires:
  - iwahori-low-gap-cluster-integralization
  - iwahori-low-gap-cluster-atomization
---

The first prerequisite supplies, after `o(d_n)` stabilization, a direct sum of
unitaries indexed by connected components of the low-gap bipartite graph.  It
is `o(1)` from the original identity identification, has vanishing aggregate
Iwahori intertwining defect, and never transports mass between distinct
components.

Apply `iwahori-low-gap-cluster-atomization` inside each component.  Its
orthogonal summands lie in individual isotypic block pairs `(P_(n,i),Q_(n,j))`
with `lambda_(n,i,j)<a_n`, have equal physical dimensions, and preserve both
the `o(1)` distance to the identity and the vanishing aggregate mixed defect.
Combining the two `o(d_n)` stabilizations is still `o(d_n)`.  The resulting
summands and block unitaries are exactly the conclusion required by
`iwahori-fractional-transport-integralization`.

Thus the former three-part operator-matching obstruction has been reduced to
one: **monomialize a unitary inside a connected cluster of low-gap Iwahori
types**.  Cross-cluster physical rank, dimension balance, and global polar
rounding are already settled.