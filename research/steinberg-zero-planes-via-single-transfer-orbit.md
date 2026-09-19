---
rg: 2
id: steinberg-zero-planes-via-single-transfer-orbit
kind: route
title: Iterate the one projective zero-plane transfer from b=-1
target: steinberg-three-zero-families-propagate-all-chords
requires:
  - steinberg-zero-marginal-kills-b-minus-one-plane
---

Starting from the full zero plane `b=-1`, repeatedly use the relation
between `4B` and `4B/(1-4B)` until every nonzero `b`-plane is zero, then
use the plane marginal and the source identity to kill `b=0` and `c=0`.

This route is invalidated for every odd `p>=7` by
`steinberg-plane-transfer-stalls-at-large-primes`: the recurrence only
equates the two candidate planes, rather than moving directly from `B` to
either one, and neither candidate is initially known.  The same route does
close `p=3,5`.  A uniform proof needs a second seed plane or a distinct
transfer relation.
