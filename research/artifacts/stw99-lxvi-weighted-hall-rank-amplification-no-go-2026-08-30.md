---
title: STW LXVI analytic audit --- weighted Hall and the one-branch rank-amplification no-go (2026-08-30)
---

## Higher-rank Euler/Hall criterion

For finite coordinate sets `S_j` and demands `r_j>=1`, consider

`Xi=direct_sum_j L_(S_j)^(direct_sum r_j)`.

Its Euler class is

`product_j (sum_(i in S_j)x_i)^(r_j)`.

It is nonzero exactly when

`|union_(j in F)S_j| >= sum_(j in F)r_j`

for every `F`.  This is ordinary Hall applied after replacing `S_j` by
`r_j` labelled copies.  It is the exact demand-capacity invariant for the
triangular Hopf blocks.

## Non-uniform diagonal maps still fail

Duplicating the entire branch list is unnecessary for the obstruction.
Suppose an early simplicity stage supplies infinitely many summands whose
noncommon coordinate supports have uniformly bounded size `u`; the (C2)
singleton branches do exactly this.  Follow all of them through one common
later branch history, choosing only the distinguished rank-doubling corner
whenever a new triangular depth is added.  At a fixed late stage their
supports lie in `T union U_j`, with `T` finite and common and
`|U_j|<=u`, while their common rank is `R=2^c r_0`.

Once `R>u`, choose `m>|T|/(R-u)`.  A group of `m` histories has rank `Rm`
but uses at most `|T|+um<Rm` coordinates.  Weighted Hall fails.  More
strongly, rank exceeds half the real base dimension, so the group bundle
has a nowhere-zero section and dominates `g`.  Infinitely many disjoint
groups give a strict `direct_sum_infinity g` below the image of the seed;
Rordam Lemmas 4.2--4.3 make that image equivalent to the multiplier unit.

Thus the natural analytic implementation of the feasible K-theory
triangle is a no-go: one cofinal rank-amplifying path already makes the
seed properly infinite, even when every other branch is unpaired.  A
surviving construction would need to prevent any infinite bounded-support
family from sharing a cofinal rank-amplifying continuation.  In a standard
diagonal endomorphism every branch acts on every summand, so this requires
an architecture beyond the present Rordam diagonal framework.
