---
rg: 2
id: pauli-packet-incoming-mass-exceeds-corner-capacity-proof
kind: route
title: Sum the exact transported-coefficient block masses and apply the contraction capacity identity
target: pauli-packet-incoming-mass-exceeds-corner-capacity
requires:
  - transported-coefficient-raw-character-isotropic-mixing
  - contraction-branch-capacity-forces-collision
artifacts:
  - experiments/verify_pauli_incoming_mass.py
---

The exact `T_0` block table sums to `3/8`, and the `T_1` table sums to
`1/4`.  These are the squared HS masses of `QT_0Q` and `QT_1Q`; their sum is
`5/8`, while `tau(Q)=4(1/8)=1/2`.  Substitution into `(CBC1)` gives
`(5/8)^2/(1/2)-5/8=5/32`.
