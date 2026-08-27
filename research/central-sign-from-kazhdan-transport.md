---
rg: 2
id: central-sign-from-kazhdan-transport
kind: route
title: Derive the central-sign obstruction from Kazhdan transport
target: central-sign-corona-obstruction
requires: [kazhdan-asymptotic-commutant-transport]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/KazhdanSignCriterion.lean
---

## Why sufficient

If a corona model detects the central involution, its negative spectral
corner is a positive-rank matrix corona on which that involution is `-1`.
The centralizer element is an asymptotic commutant; Kazhdan transport makes
its displacement another asymptotic commutant, so the defining commutator
and its square converge to `1` in normalized Hilbert--Schmidt norm.  The
square is simultaneously the scalar `-1`, at distance `2`, a contradiction.
