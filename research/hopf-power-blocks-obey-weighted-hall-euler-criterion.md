---
rg: 2
id: hopf-power-blocks-obey-weighted-hall-euler-criterion
kind: claim
title: Direct sums of Hopf-power blocks have nonzero Euler class exactly under weighted Hall
distinct_from:
  dyadic-rordam-identical-pairing-destroys-sdr: that treats repeated rank-one line-bundle sets in the refuted paired design; this gives the exact arbitrary-rank demand version needed for triangular blocks.
  triangular-hopf-bundles-admit-coherent-dyadic-euler-roots: that constructs one coherent finite triangle and verifies each individual block; this characterizes when arbitrary finite sums of such blocks retain a nonzero total Euler class.
artifacts:
  - research/artifacts/stw99-lxvi-weighted-hall-rank-amplification-no-go-2026-08-30.md
---

Let `S_1,...,S_t` be finite coordinate sets and let `r_1,...,r_t` be
positive integers.  On a product of two-spheres containing all these
coordinates, put

`L_(S_j)=tensor_(i in S_j) H_i`

and

`Xi=direct_sum_(j=1)^t L_(S_j)^(direct_sum r_j)`.

Then `e(Xi)` is nonzero in integral cohomology if and only if

`|union_(j in F) S_j| >= sum_(j in F) r_j`                 `(WH)`

for every subset `F` of `{1,...,t}`.

Equivalently, the coordinate sets admit disjoint demand sets
`R_j subset S_j` with `|R_j|=r_j`.  Thus Rordam's rank-one
system-of-distinct-representatives criterion is the case `r_j=1`; the
correct higher-rank invariant is weighted Hall, not the cardinality of
each block separately.
