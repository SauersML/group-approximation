---
rg: 2
id: atlas-a4-packet-letters-generate-both-a8-charts
kind: claim
title: The thirty shortest A4 contexts use generating sets of both A8 charts
artifacts:
  - experiments/atlas_a4_packet_generation.py
---

Take the thirty shortest pair-cubes of `atlas-shortest-a4-triangle-packet`.
For each chart factor separately, collect the distinct chart elements which
occur as one of the two repeated letters in those contexts.  Then that finite
set generates the entire chart group

```text
GL(4,2) ~= A8,
```

of order `20160`.

In the exact radius-five packet there are ten distinct participating letters on
each factor, of orders two and three, and exact closure under multiplication
gives

```text
|<packet letters in factor 1>| = 20160,
|<packet letters in factor 2>| = 20160.                (A4-PACKET-GEN)
```

Thus the thirty A4 contexts are globally spanning on **both** chart sides.
Any agreement theorem which synchronizes the local chart actions on every
packet letter automatically controls the complete A8 actions; there is no
unseen chart subgroup on which a high-dimensional alignment can escape.