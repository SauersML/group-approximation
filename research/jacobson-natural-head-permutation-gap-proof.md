---
rg: 2
id: jacobson-natural-head-permutation-gap-proof
kind: route
title: Follow two natural head points and verify an exact 56-point tail-braid certificate
target: jacobson-natural-head-permutation-gap-is-sqrt-three
requires:
  - jacobson-joint-cells-are-two-braids
  - jacobson-tail-braid-exactification-and-standard-carrier
artifacts:
  - research/artifacts/jacobson-natural-head-permutation-gap-2026-09-08.md
  - research/artifacts/jacobson-56-point-two-braid-2026-09-08.json
  - experiments/jacobson_56_point_two_braid_search.py
---

The natural seven-point head has one fixed overlap point and two natural
three-point overlap orbits. Equivariance gives a complete description
of every allowed permutation involution. If the first braid fixes all
points with head coordinate `e_2`, that description forces the involution
to exchange the two three-point orbit families. Applying the same braid
at head coordinate `e_1` then gives head coordinate `e_1+e_3`, a
contradiction. Every nonidentity permutation has norm distance at least
`sqrt(3)` from the identity.

The artifact gives the tail action on eight cosets, the overlap
involution, and every cycle of `HB`. The tail braid is exact; `HB`
has only cycles of lengths one, three, and nine, including nine-cycles.
Thus its first-braid defect is exactly `sqrt(3)`, and the marked
negative rank is sixteen. This establishes sharpness in the stated
permutation class and the upper bound for the unrestricted infima.
The accompanying exact-integer MSI replay exhausts all 606177
exact-tail involutions on that packet and independently verifies the
displayed certificate. No conclusion about all-unitary positivity is
used or inferred.
