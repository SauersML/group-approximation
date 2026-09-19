---
rg: 2
id: leavitt-degree3-formal-corner-cycle-is-absent
kind: claim
title: The degree-three length-eleven cover has no literal minimal long-corner cycle
artifacts:
  - research/artifacts/check-degree3-formal-corner-core.py
distinct_from:
  leavitt-degree3-direct-pivot-screen-is-empty: that uses the actual Bergman packet and tests a direct central target; this topology theorem treats distinct formal coefficient letters and the joint two-unary incidence.
---

For every degree-three length-eleven cyclic sign word with orbit valences
`(1,1,9)`, the nine-valent orbit has corner-size multiset

```text
(1,1,1,1,1,1,1,1,3).
```

Replace seven coefficient slots by distinct free letters and the other four
by identities.  Across all eleven sign topologies and all `C(11,4)=330`
identity placements, neither orientation of both unary long corners occurs
among the nine target corners.  Hence the sharp four-incidence cycle from
`leavitt-two-relator-corner-peeling` cannot be realized by literal formal
corner equality in this shortest topology.

This does not exclude equality caused by the special Leavitt packet
relations.  It narrows the exact search to genuinely algebraic corner
collisions rather than cyclic incidence alone.
