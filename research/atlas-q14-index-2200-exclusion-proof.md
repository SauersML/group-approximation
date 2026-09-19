---
rg: 2
id: atlas-q14-index-2200-exclusion-proof
kind: route
title: Exclude the HS equality cell and cross index two thousand two hundred
target: atlas-q14-simple-overgroup-index-is-at-least-2201
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-2200
  - atlas-hs-s8-derived-packet-collision-exclusion
---

At equality in `(OSI2200)`, both marked charts are S8-derived A8 subgroups in
`HS`; the normalizer absorbs graph marking, so one conjugator family suffices.
The exact five-cell screen in `(HSD2)` excludes every such conjugator already
with packet plus collision 19243.  Adding q14 cannot restore a survivor, so
the equality case is removed and `(OSI2201)` follows.

