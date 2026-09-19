---
rg: 2
id: two-magic-square-incidence-overlaps-never-separate
kind: claim
title: Two Magic-Square incidence blocks can have an infinite universal group but never a perfect finite-versus-commuting gap
artifacts:
  - research/two-square-incidence-overlap-classification-proof.md
distinct_from:
  magic-square-one-port-is-a-universal-phase-absorber: that treats operator-valued boundary ports; this classifies closed scalar-sign degree-two incidence networks.
  two-port-magic-square-commutator-is-holonomy-square: that classifies two operator ports inside one square; this treats two square subgraphs glued along context vertices.
  row-glued-magic-squares-absorb-noncommuting-ports: that identifies cell observables across blocks and leaves the degree-two incidence class; this result does not cover such higher-occurrence variables.
---

Regard a Magic Square as the graph-incidence LCS on `K_(3,3)`: contexts are
vertices and cell variables are edges.  Form a simple two-block overlap by
taking two copies of `K_(3,3)` whose left context sets meet in `r` vertices and
whose right context sets meet in `c` vertices, identifying all common edges.
Write the union as

```text
G_(r,c)=K_(3,3) union_(K_(r,c)) K_(3,3).
```

Up to swapping the two bipartitions, the proper connected overlap types and
their homogeneous incidence-group status are

```text
overlap       union/minor witness                  Gamma(G_(r,c))
(3,2)         K_(3,4)                              finite
(3,1)         K_(3,5)                              finite
(3,0)         K_(3,6)                              infinite
(2,2)         two vertex-disjoint 4-cycles         infinite
(2,1)         two vertex-disjoint 4-cycles         infinite
(2,0)         two vertex-disjoint 4-cycles         infinite
(1,1)         two vertex-disjoint 4-cycles         infinite
(1,0)         two vertex-disjoint 4-cycles         infinite
```

The omitted `(3,3)` case is one square, `K_(3,3)`.  The classification follows
from Paddock--Russo--Silverthorne--Slofstra, *Algebraic Combinatorics* 6
(2023), Theorem 1.4: a graph incidence group is finite exactly when its graph
has neither two vertex-disjoint cycles nor a `K_(3,6)` minor.  In particular,
a finite network of Magic-Square contexts need not reduce to a finite
extraspecial/Clifford group; the first common-bipartition two-block example
`K_(3,6)` is already infinite.

Nevertheless **none** of these scalar-sign networks gives the desired
perfect finite-versus-commuting separation.  For every graph-incidence LCS
`(G,b)`, the marked central sign `J` is nontrivial in the universal group if
and only if it is nontrivial in a finite-dimensional representation
(Paddock et al., Corollary 4.7, equivalently Arkhipov's theorem).  Hence

```text
omega^co(G,b)=1  iff  omega^q(G,b)=1.
```

The infinite cases enlarge the universal group but not the perfect marked
sector.  A surviving two-cycle decoder must therefore leave closed
degree-two scalar graph-incidence syntax: it needs operator-valued ports,
a variable occurring in more than two contexts, or another coupling whose
source relation is not merely a vertex sign profile.
