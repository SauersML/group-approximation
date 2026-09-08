---
rg: 2
id: order-two-low-rank-via-properly-infinite-corner
kind: route
title: Dead. Try to close the low-rank order-two case with a properly infinite corner
target: order-two-universal-non-mf-at-ranks-two-and-three
requires: []
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**DEAD.**  Invalidated by
`order-two-universal-ring-has-no-infinite-corner`.

## The attempt

`properly-infinite-corner-forces-non-mf-from-rank-two` reaches rank two
and needs no ambient fullness, which is exactly what a torsion defect
cannot have: a full defect dies in any nonzero commutative quotient, and
`A_2` surjects onto `Z[z,z^(-1)]`.  So the certificate looks like the
right instrument for this ring, and it is the only fullness-free route in
the graph that reaches rank two at all.

The natural strengthening is to look in `M_d(A_2)` rather than `A_2`,
since `EL_n(M_d(A_2))` sits inside `EL_(nd)(A_2)` and a certificate at
any finite `d` would suffice.

## Why it dies

`order-two-universal-ring-has-no-infinite-corner` proves there is no
nonzero properly infinite idempotent in any `M_d(A_2)`.  The integral
symbol of a candidate `p` dies over `Q(z)` by a split-injection dimension
count, which drops `p` into the binary finitary layer; the corner that
survives is then a finite ring, where the same count applies again.

The same statement also kills the indirect version of this attempt —
descending the established rank-four answer through
`elementary-rank-descent-to-two`, whose hypothesis is the case `p = 1` of
the certificate.  Both failures have one cause, and it is a dimension
count rather than a missing construction, so no sharper certificate
recovers the route.
