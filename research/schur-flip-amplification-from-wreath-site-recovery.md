---
rg: 2
id: schur-flip-amplification-from-wreath-site-recovery
kind: route
title: Recover supercritical flip rank from one compressor's infinite new-site family
target: compressor-amplifies-schur-flip-cocycle-rank
requires:
  - schur-flip-wreath-compressor-has-infinite-cocycle-rank
  - matrix-recovery-of-schur-flip-wreath-sites
  - scaled-kazhdan-transport
  - projective-holonomy-rank-forces-exponential-multiplicity
---

The wreath theorem supplies an exact finite-tracial model and arbitrary
binary cocycle rank after one strict compressor, so completeness and depth
independence are built in.  The matrix-recovery theorem selects more than
`log_2 m` independent local flip squares on the current forbidden
multiplicity carrier with total error controlled at that carrier's scale.
Scaled Kazhdan transport returns the recovered coefficient modules without
ambient-dimension loss.  The projective-holonomy rank theorem then forces
`2^n|m` with `n>log_2 m`, impossible.  Hence the alternative is a fixed
relator-energy floor, which is `(SFA1)`.

