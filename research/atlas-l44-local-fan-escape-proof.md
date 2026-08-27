---
rg: 2
id: atlas-l44-local-fan-escape-proof
kind: route
title: Enumerate the two L4(4) fan fibers and the H6 rectangle
target: atlas-l44-local-packet-fans-do-not-force-subfield-support
requires:
  - atlas-a4-packet-biclique-decomposition
artifacts:
  - experiments/atlas_a4_l44_fan_escape.py
---

Lift the certified binary packet matrices entrywise to `GF(4)`.  Enumerate
the conjugacy class of one packet involution, test the appropriate adjacent
cube equations for each biclique, and recognize the subfield by the exact
entrywise condition `z^2=z`.  For `H6`, enumerate ordered pairs of surviving
involutions, impose their internal order-three products and the reverse fan.
The assertion-hardened replay gives `(L44F-1)--(L44F-2)`.

