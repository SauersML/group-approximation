---
rg: 2
id: atlas-l44-h6-spectrum-blindness-proof
kind: route
title: Histogram the H6 product polynomial on the exact rectangle fiber
target: atlas-l44-h6-spectrum-is-blind-on-all-rectangle-pairs
requires:
  - atlas-l44-local-packet-fans-do-not-force-subfield-support
artifacts:
  - experiments/atlas_a4_l44_fan_escape.py
---

The existing exact rectangle enumeration now records and assertion-checks
the characteristic polynomial of the ordered involution product for every
survivor.  Its histogram has one bin only, `(L44S-1)`, of multiplicity
`1262`.  Factoring that polynomial over `F4` gives the stated source spectrum
and proves the no-go.

