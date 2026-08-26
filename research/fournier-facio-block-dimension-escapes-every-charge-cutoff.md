---
rg: 2
id: fournier-facio-block-dimension-escapes-every-charge-cutoff
kind: claim
title: Every Fournier--Facio common-block witness must put all charge at diverging block dimension
invalidates:
  - fournier-facio-tight-unbounded-block-near-witness
distinct_from:
  fournier-facio-bounded-block-near-witness-impossible: That excludes one global uniform block bound; this allows arbitrary finite block sizes and proves that every fixed bounded-size stratum has charge zero.
  fournier-facio-charge-null-monomial-perturbations-impossible: That treats one-dimensional fibers with arbitrary null mixing; this permits arbitrary growing matrix fibers and locates exactly where their charge must live.
  fournier-facio-purely-singular-free-near-representation: That is the open existence claim; this is a necessary escape-to-infinity law for the surviving common-block architecture.
---

**ESTABLISHED DIMENSION-ESCAPE LAW.**  Suppose a charged-basis candidate for
the Fournier--Facio group is charge-null close to block-monomial actors over
one common partition

```text
X=disjoint_union_(y in Y) X_y,             1<=d(y)=|X_y|<infinity. (FDE1)
```

Let `nu` be the pushed probability charge on `Y`.  Then necessarily

```text
nu({y:d(y)<=m})=0,
nu({y:d(y)>m})=1                         for every finite m.       (FDE2)
```

In particular the block-dimension distribution cannot be tight, cannot be
countably additive, and cannot give positive charge to any fixed finite list
of matrix sizes.  This conclusion still permits arbitrary matrix-valued
internal cocycles, noncompact charge-null perturbations, and block sizes
which vary without bound.

Indeed block-monomial unitaries can only transport blocks of equal dimension,
so every cutoff `{d<=m}` is invariant under every underlying block
permutation.  If one cutoff had positive charge, restricting and normalizing
the charge there would give a charge-null perturbation of a uniformly
bounded block-monomial Fournier--Facio witness.  This is excluded by
`fournier-facio-bounded-block-near-witness-impossible`.

Thus an unbounded-block positive construction must use a genuinely
finitely-additive dimension-at-infinity charge.  Merely taking a sequence of
larger finite blocks is not enough unless the invariant charge annihilates
every bounded initial segment.

Proof: `fournier-facio-block-dimension-escape-proof`.
