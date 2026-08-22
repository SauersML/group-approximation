---
rg: 2
id: atlas-o8m2-a8-carrier-fusion-proof
kind: route
title: Fuse the orthogonal and direct-factor A8 carriers in degree 119
target: atlas-o8m2-has-one-a8-class-with-c3-centralizer
requires:
  - atlas-a8-index-33-to-89-is-orthogonal-sp6
artifacts:
  - experiments/atlas_o8m2_a8_carrier_audit.py
  - experiments/atlas-o8m2-a8-carrier-audit.json
---

Choose a maximal subgroup containing an arbitrary `A8<G`.  Lagrange and the
[ATLAS maximal-subgroup table](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/O8-%282%29.html)
leave exactly `(OMC2)`.  Inside `S6(2)`, the required input proves that every
`A8` is the derived subgroup of the unique orthogonal `S8` class.  Inside
`M=(3 x A8):2`, projection to `M/A8 ~= S3` kills every simple `A8` subgroup;
hence it lies in, and equals, the displayed normal `A8` factor.

It remains only to decide ambient fusion.  The replay constructs
`PrimitiveGroup(119,1)`, takes exact representatives of the two maximal
classes, constructs the two `A8` subgroups just described, and asks GAP for
ambient conjugacy.  They fuse.  GAP then returns normalizer order `120960`
and centralizer order `3`; assertions pin both values.  Orbit-stabilizer and
the known `S8` normalizer inside `S6(2)` give `(OMC3)`.  Since the two carrier
sources exhaust every `A8`, this proves `(OMC1)` and uniqueness.

