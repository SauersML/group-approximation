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

**DEAD** (2026-09-18). Its third input,
`garside-odometer-groups-have-simple-finite-index-commutator`, is REFUTED by
`garside-decorated-groupoids-hide-artin-groups-in-isotropy`. The compiler
invalidates this route automatically.
- The groupoid is not effective: Li's boundary of `A^+` is a point, and
  `ker(ℓ)` lies in the isotropy.
- No simple subgroup of the host contains the Artin group.

The original plan, kept for the record:
1. `F_P` is F_infinity (Li's theorem). This still stands.
2. `A` embeds in `F_P`. This is true, but only through isotropy.
3. `D(F_P)` is simple of finite index. This is false.
