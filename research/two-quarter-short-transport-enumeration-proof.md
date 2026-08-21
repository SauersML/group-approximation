---
rg: 2
id: two-quarter-short-transport-enumeration-proof
kind: route
title: Replay the exact length-two atlas word enumeration
target: two-quarter-carriers-resist-short-packet-transport
requires: []
artifacts:
  - experiments/atlas_quarter_carrier_short_conjugacy.py
  - experiments/atlas-quarter-carrier-short-conjugacy.json
---

Reduce the identity, the eight named generators, and every ordered product of
two generators in the exact rational Leavitt-prefix algebra.  Duplicate
reduced expressions are merged, leaving 48 distinct keys.  For each key `g`,
evaluate the exact rational trace of `F_cap g F_branch g*`.  The committed
certificate records maximum `1/16`, attained already at the statistically
independent placement, and no overlap `1/4`; hence none of the enumerated
words conjugates the two trace-quarter projections.
