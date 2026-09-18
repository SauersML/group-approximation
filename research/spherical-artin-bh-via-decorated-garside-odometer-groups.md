---
rg: 2
id: spherical-artin-bh-via-decorated-garside-odometer-groups
kind: route
title: Finite-type Artin groups embed in the simple commutator subgroup of an F_infinity decorated Garside odometer full group
target: spherical-artin-groups-satisfy-boone-higman
requires:
  - decorated-garside-odometer-full-groups-are-type-f-infinity
  - artin-groups-embed-in-decorated-garside-odometer-groups
  - garside-odometer-groups-have-simple-finite-index-commutator
---

This is a second route to `spherical-artin-groups-satisfy-boone-higman`. It is
independent of the characteristic-zero linear chain that the node currently
rests on, whose literature status bh-lit flagged in finding F1.

1. **Finiteness (established).** `decorated-garside-odometer-full-groups-are-type-f-infinity`,
   a lane proof via Li arXiv:2110.04505, gives the F_infinity group `F_P`.
2. **Embedding (established).** `artin-groups-embed-in-decorated-garside-odometer-groups`,
   a lane proof, puts `A` inside it. Faithfulness is imported from
   Belk--Bleak--Chatterji--Matucci--Perego, Theorem 2.4.
3. **Simplicity (OPEN).** `garside-odometer-groups-have-simple-finite-index-commutator`
   supplies it: `D(F_P)` is simple of finite index, and `A` embeds in it by the
   disjoint-copies argument recorded in that node.

Artin groups with one generator (`Z`) are trivial cases. The route is OPEN
until step 3 is proved.
