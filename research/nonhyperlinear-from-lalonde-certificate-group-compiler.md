---
rg: 2
id: nonhyperlinear-from-lalonde-certificate-group-compiler
kind: route
title: Turn Lalonde's exact tracial certificate into a marked non-hyperlinear group
target: non-hyperlinear-group
requires:
  - lalonde-certificate-gives-dimension-free-tracial-gap
  - lalonde-certificate-common-carrier-group-compiler
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

Use the group presentation supplied by
`lalonde-certificate-common-carrier-group-compiler`.  Its perfect
nontracial strategy proves that the marked word is nontrivial.  If the
group were hyperlinear, canonical microstates for that mark would decode
to finite-matrix tracial tuples with relation defect and Lalonde losing
energy tending to zero.  This contradicts the dimension-free gap in
`lalonde-certificate-gives-dimension-free-tracial-gap`.

The route exploits an unusually small exact rational certificate, but its
one open dependency still contains the hard vector-state/common-carrier
groupification step.  The certificate alone is not an unconditional
non-hyperlinear group.
