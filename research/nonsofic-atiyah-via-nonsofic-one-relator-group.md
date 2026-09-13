---
rg: 2
id: nonsofic-atiyah-via-nonsofic-one-relator-group
kind: route
title: A nonsofic one-relator group is a nonsofic torsion-free Strong Atiyah group
target: nonsofic-group-satisfying-strong-atiyah
requires:
  - nonsofic-one-relator-group
  - one-relator-groups-satisfy-strong-atiyah
---

Let `G` be a nonsofic one-relator group ([[nonsofic-one-relator-group]]).

* **Torsion-free.** One-relator groups with torsion are virtually special, and
  virtually special groups are sofic. This is the printed derivation quoted in
  [[one-relator-groups-satisfy-strong-atiyah]]. `G` is not sofic, so it is
  torsion-free.
* **Strong Atiyah.** Corollary 1.3 of Jaikin-Zapirain--Lopez-Alvarez gives Strong
  Atiyah over `C` for `G`. With no torsion, the values are integers.

So `G` witnesses [[nonsofic-group-satisfying-strong-atiyah]]. The route is idle
until a nonsofic one-relator group is found; it records that such a group would
be the first nonsofic group known to satisfy Strong Atiyah.
