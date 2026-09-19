---
rg: 2
id: bounded-conductor-width-pays-uniform-first-exit
kind: claim
title: Bounded conductor width forces a uniform first-exit mass
distinct_from:
  folner-multiplicity-atlases-have-vanishing-first-exit: that constructs triangular profiles of growing width with first-exit mass tending to zero; this proves the converse lower bound and shows that unbounded conductor spread is necessary and order-sharp.
  weyl-kernel-joins-descend-two-levels-without-mass-contraction: that shows arbitrary mass can already lie in a shallow common quotient and defeats a fixed contraction; this bounds the overlap of a profile with its translated copy when only finitely many conductor bands are occupied.
  periodic-conductor-plateaux-pay-a-shared-root-seam: that charges block-diagonal periodic root reservoirs through a literal shared-root word; this charges rectangular Schur transport directly through the boundary of its conductor support.
---

ESTABLISHED.  Let `mu=(mu_j)_(j in Z)` be a probability profile on conductor
depths, extended by zero outside its support, and suppose at most `B` depths
have positive mass.  For the unit depth shift `S mu`,

```text
TV(mu,S mu) >=1/B.                                      (BCW1)
```

Consequently, consider two exact semisimple conductor atlases whose
normalized dimension weights are `mu_j` and `mu_(j-1)`.  Any exact partial
intertwiner between them has source trace at most

```text
sum_j min(mu_j,mu_(j-1))
 =1-TV(mu,S mu) <=1-1/B.                               (BCW2)
```

Thus its first-exit mass is at least `1/B`.  The same conclusion holds for a
multidimensional coweight profile whenever its projection onto one root-depth
coordinate occupies at most `B` values: total variation decreases under
marginalization, so the one-dimensional bound applies.

Tensoring the atlas with the native four-atom algebra does not alter this
loss.  Therefore any rectangular-transport counterarchitecture for the
two-primary native sector whose first-exit mass tends to zero must occupy an
unbounded number of conductor depths in every active shift direction.  A
bounded-width exact sector cannot realize the solenoidal escape.

This is a sharp interface theorem, not the full native defect inequality.
The triangular profiles of
`folner-multiplicity-atlases-have-vanishing-first-exit` occupy `N+1` depths
and have first exit `O(1/N)`, matching `(BCW1)` up to a fixed constant.  What
remains open is to decode the actual arithmetic root packets into one such
common conductor atlas; after that decoding, `(BCW1)` supplies the desired
uniform payment on every bounded-width part.
