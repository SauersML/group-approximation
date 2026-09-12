---
rg: 2
id: atlas-q14-index-11881-through-12144-exclusion-proof
kind: route
title: Jump through the M24 equality endpoint
target: atlas-q14-simple-overgroup-index-exceeds-12144
requires:
  - atlas-q14-simple-overgroup-index-exceeds-11880
  - atlas-a8-index-11881-to-12144-reaches-m24
  - atlas-m24-a8-three-carrier-fork
  - atlas-m24-marked-packet-collision-exclusion
---

The first input starts beyond index `11880`; the second leaves only `M24` at
index `12144`; the third gives the exact finite carrier fork; and the fourth
excludes every marked pair at that equality.  Together they prove
`(OSI12145)`.

