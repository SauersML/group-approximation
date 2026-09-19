---
rg: 2
id: atlas-q14-index-9792-exclusion-proof
kind: route
title: Exclude the O8-(2) equality endpoint
target: atlas-q14-simple-overgroup-index-exceeds-9792
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-9792
  - atlas-a8-index-8641-to-9792-reaches-o8m2
  - atlas-o8m2-packet-collision-exclusion
---

The first two inputs isolate equality as `O8-(2)`.  The last input excludes
every marked pair already using packet plus collision, proving `(OSI9793)`.

