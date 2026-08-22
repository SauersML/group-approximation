---
rg: 2
id: atlas-m24-marked-packet-collision-exclusion-proof
kind: route
title: Exclude the M24 equality by packet confinement to one affine carrier
target: atlas-m24-marked-packet-collision-exclusion
requires:
  - atlas-m24-packet-survivors-share-octad-and-19243-kills-all
---

The input proves that every packet-compatible marked pair lies in one common
octad stabilizer `2^4:A8`, hence cannot generate the simple ambient group
`M24`.  It also proves the stronger statement that collision `19243` kills
all residual packet models.  Therefore no augmented generating pair exists.

