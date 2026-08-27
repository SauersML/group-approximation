---
rg: 2
id: two-kl-gate-orbit-has-identity-fiber-obstruction
kind: claim
title: Every two-coordinate KL conjugator leaves the identity fiber odd
distinct_from:
  kl-gate-corner-test-is-an-even-unit-fiber-audit: that rejects one KL gate and single coefficient-one roots; this rejects the first genuinely two-mixed-gate family.
  inverse-packet-conjugator-must-mix-s-and-t-charts: that is only a necessary chart condition; these conjugators pass it but fail a sharper group-basis coefficient test.
  both-rank-three-factors-must-be-packet-corrected: that derives the correction equation; this computes one coefficient throughout a concrete two-gate orbit.
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

Let `q_i=phat^i qhat phat^-i`, `x=q_iq_j`, and use the inverse-pair packets
`P_x`, `P_(x^-1)`.  The anchored family reduces to nineteen nonzero relative
distances, but cyclic conjugation need not preserve the fixed corner lifts;
the exact Bergman audit therefore checks all 380 ordered off-diagonal pairs
and gives

```text
[1]Delta=1,
[1](A P_(x^-1))=[1](P_x B)=[1](P_x P_(x^-1))=0
```

for every ordered pair (the diagonal has `x=1`).  Thus the identity coefficient
of the correction defect is always one.  No product of two coordinate
conjugates of the KL gate solves the inverse-pair corner equation.
