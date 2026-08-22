---
rg: 2
id: atlas-m24-a8-fusion-proof
kind: route
title: Fuse all M24 A8 carrier sources through the canonical octad complement
target: atlas-m24-has-one-self-normalizing-a8-class
requires:
  - atlas-m24-a8-three-carrier-fork
  - atlas-a8-index-91-to-496-reaches-standard-l5
artifacts:
  - experiments/atlas_m24_affine_a8_fusion.py
  - experiments/atlas-m24-affine-a8-fusion.json
---

Start from the three-carrier fork.  If `A8` lies in a duad stabilizer
`M22:2`, simplicity makes its action on the invariant two-set trivial, so it
lies in the pointwise stabilizer `M22`.  The ATLAS maximal-subgroup argument
recorded in the second input shows that `M22` contains no `A8`: its only
maximal order-compatible socle is the equal-order, nonisomorphic `L3(4)`.

If `A8` lies in an octad stabilizer `V:A8`, its intersection with the normal
four-dimensional 2-group `V` is normal and hence trivial.  Projection to the
quotient is therefore an isomorphism, so it is a complement.  The replay
constructs `M24` in degree 24 and the canonical octad directly, without any
maximal-subgroup enumeration.  `ComplementClassesRepresentatives` returns
one carrier class.  GAP then verifies its orbit lengths, ambient normalizer,
and centralizer, with assertions pinning every value in `(M24F-1)--(M24F-2)`.

Finally the complement fixes one point outside its octad, so it lies in an
`M23` point stabilizer.  The second input proves that `M23` has only its
maximal degree-506 `A8` class.  Thus the M23 and affine sources fuse, while
the duad source is empty.  These exhaust all sources, proving uniqueness.

