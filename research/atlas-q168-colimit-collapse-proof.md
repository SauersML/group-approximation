---
rg: 2
id: atlas-q168-colimit-collapse-proof
kind: route
title: Freeze each marked PSL3(2) multiplication table and enumerate its exact seam colimit
target: atlas-q168-rectangles-collapse-fj-seam
requires:
  - atlas-a5-seam-obstruction-is-not-universal
artifacts:
  - experiments/atlas_a4_non_a5_fj_colimits.g
  - research/artifacts/atlas-a4-q168-fj-colimits.json
---

The GAP verifier starts from the complete local low-index list and retains
the six faithful images of order 168 with trivial intersection between their
two radial `S3` subgroups.

For each marked permutation group it calls
`IsomorphismFpGroupByGenerators(Q,[r,y,u,b])`.  The resulting exact finite
presentation uses respectively 9, 10, or 11 relators.  Mapping those relators
to a six-generator free group freezes the complete marked multiplication of
`Q`, rather than merely retaining the four rectangle cubes.

The verifier then adjoins exactly the first-packet and collision relations in
`(Q168-COL-1)` and calls GAP's exact `Size` algorithm on the resulting
finitely presented colimit.  All six calculations terminate with order 168.
Direct subgroup closure inside each colimit gives the five remaining entries
of `(Q168-COL-2)`.  Since the canonical map from the order-168 local vertex
to an order-168 colimit has image of order 168, it is injective; the failures
of `F` and `J` are therefore genuine seam collapse rather than failure of the
chosen rectangle vertex.
