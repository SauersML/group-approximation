---
rg: 2
id: jacobson-mixed-packet-attains-rank-eight-below-two
kind: claim
title: An exact mixed packet attains marked rank eight with both braid defects below two
artifacts:
  - research/artifacts/jacobson-mixed-packet-certificate-2026-09-07.md
  - experiments/jacobson_mixed_cyclotomic_certificate.py
  - research/artifacts/jacobson-mixed-cyclotomic-replay-2026-09-07.json
distinct_from:
  jacobson-joint-cells-are-two-braids: that gives necessary rank restrictions and excludes separated factors; this constructs an admissible mixed packet with an overlap-central involution and proves both braid defects strictly below two.
  jacobson-two-braid-mixed-packet-gap: that asks whether the all-dimensions infimum is positive; this proves only a strict upper bound of two and does not assert a zero infimum.
---

For the Jacobson two-braid infimum there is an exact dimension-12 finite
packet `pi`, retaining the head mark with negative rank eight, and an
exact self-adjoint unitary `H` commuting with the finite overlap, such
that both braid defects are strictly less than two. Thus `0<=gamma<2`,
and the necessary marked-rank divisibility by eight is attained sharply.

The construction and its determinant proof use exact arithmetic over
`Q(zeta_7)`. Neither braid is claimed exact, and the positive-gap and
non-MF existence goals remain open.
