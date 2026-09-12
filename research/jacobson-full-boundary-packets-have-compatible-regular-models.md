---
rg: 2
id: jacobson-full-boundary-packets-have-compatible-regular-models
kind: claim
title: The full Jacobson five- and six-coordinate packets admit compatible regular matrix models on their entire intersection
distinct_from:
  jacobson-full-boundary-forces-six-coordinate-packet: that reconstructs the six-coordinate subgroup from the mixed relations; this computes its intersection with the existing boundary packet and realizes all their character and fixed-space profiles together.
  jacobson-double-rank-one-root-orbit-cannot-extend: that excludes a specific small root-support profile; this supplies a large faithful compatible profile for the full finite packets without asserting their remaining mixed relations.
artifacts:
  - research/artifacts/jacobson-gl6-boundary-compatible-regular-profiles-2026-09-08.md
---

In the full boundary presentation `Theta`, let

```text
B=GL_6(F_2) x delta(GL_3(F_2)),
C=C_0 x C_far ~= GL_5(F_2) x GL_3(F_2).
```

Their exact intersection is

```text
B intersect C=C_0 x delta(K_P) ~= GL_5(F_2) x GL_2(F_2).
```

On dimension `d=|B|`, the regular representation of `B` and
2016 copies of the regular representation of `C` can be identified
on this entire intersection. Both are faithful and retain the
head involution. Every finite subgroup `A` of either packet has
fixed-space dimension `d/|A|`, and its conjugation action on
matrices has fixed-space dimension `d^2/|A|`.

Thus the finite packets, their exact overlap, and their regular
character and commutant dimensions have a simultaneous finite
matrix realization. This does not assert that any choice of
intertwiner satisfies the remaining braid and TS words. It proves
no MF or non-MF assertion about `Theta`.

DERIVATION
jacobson-full-packet-regular-intersection-proof
