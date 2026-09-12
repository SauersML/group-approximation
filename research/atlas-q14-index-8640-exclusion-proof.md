---
rg: 2
id: atlas-q14-index-8640-exclusion-proof
kind: route
title: Exclude the O8+(2) equality endpoint by ten marked screens
target: atlas-q14-simple-overgroup-index-exceeds-8640
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-8640
  - atlas-a8-index-2201-to-8640-reaches-o8p2
  - atlas-o8p2-ten-marked-packet-collision-screens-are-empty
---

The first two inputs reduce equality in the index bound to `O8+(2)`.  The last
input excludes every marked chart pair in that group, proving `(OSI8641)`.

