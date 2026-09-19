---
title: STW XX checkpoint --- sublinear eigenmap metric entropy (2026-08-30)
---

## Intrinsic criterion

For a fixed early-stage finite test set `F`, the eigenmaps of a later
diagonal composite carry the pseudometric

```text
d_F(lambda,mu)=sup_y max_(a in F)
                   ||a(lambda(y))-a(mu(y))||.
```

If, along a cofinal sequence, the multiset can be covered by `o(L)` balls
whose radii tend to zero, then the limit algebra has uniform property Gamma.
The cover is converted to a partition, each cluster is divided into
`k`-packets, and at most `k-1` indices per cluster are discarded.  Thus the
exceptional proportion is at most `(k-1)N/L=o(1)`, while each packet has
diameter at most twice the covering radius.  The established Fourier-packet
theorem then applies.

The quantifiers are local enough for the usual diagonal argument: for every
early stage and finite test set one may choose its own cofinal subsequence.
No uniform subsequence over all finite sets is required.

## Genuine gain over distinct-map counting

The earlier concrete corollary used `D_(n,m)=o(L)`, where `D` is the number
of distinct eigenmaps.  Since a radius-`delta` covering number is at most
`D`, that is a special case.  The metric-entropy criterion is genuinely
broader: all `L` maps can be distinct while lying in, for example,
`sqrt(L)` clusters of diameter tending to zero.  The distinct-map ratio is
then one but the entropy ratio tends to zero.

## Villadsen boundary

The criterion still does not cover the independently variable coordinate
family in the positive-radius first-type examples.  If `lambda_i` and
`lambda_j` are two different coordinate projections from a product and a
scalar function `h` on the early base has oscillation `omega>0`, then

```text
d_{ {h} }(lambda_i,lambda_j)=omega:
```

the two coordinates can independently attain points where `h` is near its
maximum and minimum.  Consequently every ball of radius less than
`omega/2` contains at most one such coordinate map.  A positive asymptotic
mass of multiplicity-one independent coordinates therefore forces linear,
not sublinear, covering number.

This is a sharp fence for this method, not a negative solution of Problem
XX.  It rules out fixed small-diameter Fourier clustering but does not rule
out projections varying over the coincidence stratification in the uniform
2-norm completion.
