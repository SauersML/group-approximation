---
rg: 2
id: finite-packet-functoriality-has-positive-regular-profile
kind: claim
title: Every finite packet functoriality system has a strictly positive regular multiplicity profile
root: true
artifacts:
  - research/finite-packet-functoriality-has-positive-regular-profile-proof.md
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that treats edge-restriction equations on a graph of finite groups; this treats the full rational certificate system, including conjugacy, refinement, orthogonal decomposition and central spectral cuts, and proves that no base irreducible type can be annihilated by those relations.
  finite-packet-multiplicity-certificates-detect-mf-radicals: that proves what a negative rational certificate would imply; this constructs an interior primal point and therefore classifies when no such certificate can arise from packet functoriality alone.
---

Fix a finite diagram of finite groups `F_a`.  Allow all homogeneous
multiplicity relations obtained from:

1. restriction along subgroup inclusions;
2. transport along group isomorphisms and conjugacies;
3. composition of restrictions through intermediate groups;
4. orthogonal decomposition; and
5. central spectral cuts in the finite-dimensional group C-star algebras.

Let `B m=0` be any finite integer system assembled from these relations,
with one base coordinate `m_(a,pi)` for each irreducible type
`pi in Irr(F_a)` and the evident auxiliary coordinates for decomposed or cut
representations.

There is a rational solution `m^reg>=0` satisfying

```text
B m^reg=0,
m^reg_(a,pi)>0                     for every base irreducible type.   (RPF1)
```

More explicitly, choose a positive integer `D` divisible by every `|F_a|`
and set

```text
m^reg_(a,pi)=D dim(pi)/|F_a|.                                (RPF2)
```

The auxiliary coordinates are obtained by applying the indicated
decompositions and central cuts to these regular packets.

Consequently no identity

```text
-e_(a,pi)=B^T y+s,
s>=0,                                                        (RPF3)
```

can hold for a base irreducible type.  Thus ordinary finite-group packet
functoriality cannot, by itself, force any irreducible packet type to have
zero multiplicity.  This remains true after adding finitely many packet
groups, intermediate restriction stages, conjugate copies, automorphism
normalizers, or central isotypic refinements.

Any finite multiplicity certificate that annihilates a base type must
therefore use an additional relation on the multiplicity spaces themselves.
Examples of such additional data include a specified intertwiner holonomy,
a common matrix-coordinate carrier, or a return map whose source and target
supports have different finite ranks.  Character tables and restriction
matrices alone never supply that information.
