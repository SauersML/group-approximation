---
rg: 2
id: atlas-m24-a8-antiflag-cell-proof
kind: route
title: Enumerate M24 A8 double cells as exact octad anti-flag orbits
target: atlas-m24-a8-antiflag-cells-have-thirteen-generating-cross-cells
requires:
  - atlas-m24-has-one-self-normalizing-a8-class
  - atlas-m24-a8-three-carrier-fork
  - atlas-a4-m23-packet-double-coset-screen
artifacts:
  - experiments/atlas_m24_a8_antiflag_orbits.py
  - experiments/atlas-m24-a8-antiflag-orbits.json
---

The first input identifies conjugate charts with the `759*16=12144` octad
anti-flags.  The replay constructs those anti-flags directly in the natural
degree-24 `M24` action and computes stabilizer orbits under the fixed chart.
Assertions pin all eighteen signatures using fixed-point fiber, subdegree,
octad intersection, cross-incidence, and same-octad status.  Orbit-stabilizer
gives `(M24DC-2)` and `(M24DC-4)` from `20160/subdegree`.

For generation, any proper subgroup containing both charts lies in an
`A8`-compatible maximal carrier.  The second input leaves only M23 and
octad-affine carriers after removing the empty duad source.  A common M23
would give the same unique fixed point; a common affine carrier would give
the same unique octad.  Conversely those two coincidences visibly give the
five nongenerating cells.  Hence every remaining cell generates `M24`.

