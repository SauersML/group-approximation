---
rg: 2
id: kazhdan-cocycle-haagerup-relation-proof
kind: route
title: Freely stabilize the cocycle and intersect relation property T with Haagerup
target: kazhdan-finite-cocycles-cannot-enter-haagerup-actions
requires:
  - orthogonal-finite-fourier-reps-are-orbit-cocycles
---

Assume the partitions in `(OFC1)`--`(OFC3)` exist.  Let `G` act by its
ordinary Bernoulli shift on

```text
Z={0,1}^G
```

and diagonally on `X times Z`.  Replace every source projection
`p_(a,g)` by `p_(a,g) tensor 1`.  All partition and multiplication equations
remain true, because their coefficients are independent of `Z`.  They define
a pmp action `T` of `Q` on `X times Z` by

```text
T_a(x,z)=g.(x,z)             when x lies in p_(a,g).   (KCP1)
```

This action is essentially free.  If `a!=e`, `(KFC1)` and `(OFC4)` give
`mu(p_(a,e))=0`.  On each of the finitely many remaining pieces the label
`g` is nonidentity, and its fixed-point set in the Bernoulli `G`-space `Z`
is null.  Hence `Fix(T_a)` is null.

The diagonal `G`-action on `X times Z` is also essentially free.  Because
`G` is Haagerup, its orbit relation has the Haagerup property: a proper
conditionally negative definite function on `G`, evaluated on the unique
group label of each orbit arrow, is a proper conditionally negative definite
function on the relation.  Relation Haagerup property passes to subrelations
by restriction.  Equation `(KCP1)` puts the orbit relation of `T` inside this
`G`-orbit relation, so the `Q`-relation is Haagerup.

On every ergodic component, an essentially free pmp action of a
property-`(T)` group has a property-`(T)` orbit relation.  A pmp equivalence
relation which has both property `(T)` and the Haagerup property has finite
classes: the proper conditionally negative definite functions supplied by
Haagerup give almost invariant vectors, while property `(T)` makes them
uniformly bounded on each class, and properness then forces each class to be
finite.  Essential freeness would identify each class with an orbit of the
infinite group `Q`, a contradiction.  Therefore the assumed partitions do
not exist.
