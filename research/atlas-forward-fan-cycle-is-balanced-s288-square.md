---
rg: 2
id: atlas-forward-fan-cycle-is-balanced-s288-square
kind: claim
title: The remaining forward-fan cycle is one balanced S288 square holonomy
artifacts:
  - experiments/atlas_a4_forward_fan_288_square_margins.py
  - experiments/atlas_a4_agl5_q96_square_search.py
  - research/artifacts/atlas-a4-forward-fan-288-square-margins.json
  - research/artifacts/atlas-a4-agl5-q96-square-random-screen.json
---

After the faithful order-96 triangle completion, the first full-support seam
is a four-vertex square with finite vertices of orders `96,36,144,24` and edge
groups of orders `4,9,2,12`.  All four regular actions amplify to dimension
288 and all four edge restrictions have exactly matching regular
multiplicities.

Consequently there is no representation-ring, dimension, or individual-edge
obstruction.  Three edges can be aligned by regular tree amalgams; the fourth
is one exact permutation double-coset condition.  Solving that condition gives
a faithful finite carrier for the noncentral collision branch, its first core
cycle, and the 144-state forward fan.  Failure must be a genuine square
holonomy obstruction.

## Bounded affine screen

There is a natural faithful affine realization of `Q96` in `AGL(5,2)`.  An
MSI screen using 500,000 seeded random affine conjugators found no candidate
extending even the individually marked `F'` or `J` oververtices, hence no
square completion in two million requested combinations.  This is only a
bounded guide, not an exclusion theorem; exact centralizer/transporter
enumeration is required to rule out this affine ambient.
