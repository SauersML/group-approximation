---
rg: 2
id: atlas-q14-index-91-through-495-exclusion-proof
kind: route
title: Remove U4(3) and stop at the mixed-parity L5(2) boundary
target: atlas-q14-simple-overgroup-index-is-at-least-496
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-91
  - atlas-a8-index-91-to-496-reaches-standard-l5
  - atlas-a4-gl5-packet-collision-screen
---

The established lower bound starts at index 91.  The ambient overgroup
classification proves that no finite simple group contains `A8` at an index
from 91 through 495.  This immediately gives `(OSI496)`.

At equality, the same classification gives `S=L5(2)` and a single subgroup
conjugacy class.  Fixing the first chart leaves two relative graph parities.
The exact `GL5(2)` screen exhausts the same-parity family and finds collision
`q_19243` nonidentity at all 202 packet survivors.  Therefore any equality
case must have opposite parity.  Since the standard `A8` is self-normalizing,
that parity cannot be absorbed into the scanned inner conjugator.  This proves
the equality description without asserting that the mixed family survives.

