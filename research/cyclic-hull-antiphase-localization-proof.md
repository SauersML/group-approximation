---
rg: 2
id: cyclic-hull-antiphase-localization-proof
kind: route
title: Separate centralizer propagation from finite-radius cyclic-hull support
target: cyclic-hull-antiphase-has-propagation-or-radius-firewall
requires:
  - literal-antiphase-branches-recreate-regular-character-packing
---

For the propagation half, commute `R` past each reducer word and use
`RP=epsilon P`; continuity extends the scalar action from the algebraic span
of the orbit ranges to their join.  Opposite scalar actions give orthogonal
cyclic components, so the existing literal packing firewall applies whenever
the seed is a finite-subgroup character projection.

For the radius half, the two reflections in `(CHP5)` generate the cyclic
shift `ts`.  Therefore the orbit of `delta_0` spans all `d` coordinates, while
a fixed finite word set reaches at most `|W|` coordinates.  This proves the
rank and normalized-trace estimates `(CHP7)` and excludes every fixed positive
support polynomial or tight-frame lower bound.

