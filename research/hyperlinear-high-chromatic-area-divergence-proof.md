---
rg: 2
id: hyperlinear-high-chromatic-area-divergence-proof
kind: route
title: Apply the high-chromatic collapse theorem to a bounded-area subsequence
target: hyperlinear-groups-force-area-divergence-in-high-chromatic-sections
requires:
  - bounded-area-high-chromatic-conjugacy-collapse
---

If `(HAD2)` failed, some subsequence would have all edge areas bounded by one
integer `L`.  The chromatic numbers on that subsequence still tend to infinity,
and `(HAD1)` gives one uniform bound for the vertex cubes.  Increasing `L` to
the larger of the two bounds makes this subsequence satisfy all hypotheses of
`bounded-area-high-chromatic-conjugacy-collapse`.  That theorem kills `w` in
every homomorphism to a tracial matrix ultraproduct.

Hyperlinearity supplies a regular-character embedding of `G` into such an
ultraproduct.  Since `w!=1`, its image has squared normalized-HS distance `2`
from the identity, contradiction.  Thus the maximum edge area tends to
infinity.  Sofic groups are hyperlinear and amenable groups are sofic, giving
the final assertion.
