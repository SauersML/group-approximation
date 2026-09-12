---
rg: 2
id: kun-thom-clifford-wall-normal-form-route
kind: route
title: Build the wall from one compressed-commutant Majorana
target: kun-thom-clifford-relative-wall
requires: [relative-wall-commutant-growth, compressed-commutant-majorana]
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
---

**This route is one direction of an EQUIVALENCE, not a reduction.  It renames
the problem; it does not shrink it.**  Read with
`compressed-commutant-majorana-from-wall-route`, which is the other
direction.  Flagged explicitly after the team's "restatement dressed as
reduction" catch: given the established `relative-wall-commutant-growth`, the
prerequisite `compressed-commutant-majorana` is *logically equivalent* to the
target, so nothing here is closer to a construction than the target was.

What the equivalence buys is not progress on the target but a better
coordinate system for attacking it: the marked element `h` disappears, the
demand moves to the compressed subgroup `t Gamma t^(-1)`, and the
anticommutation becomes a single `Gamma`-conjugation.  That reformulation is
what makes the growth index of `compressor-growth-index-homomorphism`
applicable, and hence what yields
`commutator-compressor-carries-no-wall` -- which *is* new information.  The
value is downstream of the restatement, not in it.

Mechanically: the wall normal form turns the two normalized-Hilbert--Schmidt
conditions into one exact algebraic demand; pulling the involution back by
`Ad pi(t)^(-1)` produces a Clifford wall in the original coordinates, and
matrix representatives of a Connes-embeddable model give the finite endpoint
`(KCP12)--(KCP13)` with constant-one error.  Passing from an
almost-representation family to an exact homomorphism into a tracial matrix
ultraproduct, and back, loses nothing.
