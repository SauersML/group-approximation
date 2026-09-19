---
rg: 2
id: steinberg-p-five-kappa-from-b-zero-anchor
kind: route
title: Kill the p=5 boundary scalar using only b=0 Y rows and the X anchor
target: steinberg-fox-recurrence-forces-zero-marginals
requires:
  - steinberg-y-anchor-leaves-one-boundary-mode
---

This route is invalidated by
`steinberg-p-five-b-zero-boundary-absorber`.  The complete `b=0` Y system
and all five `X(1,0,c)` equations admit an explicit solution with arbitrary
nonzero `kappa`; the apparent final residual is the omitted projective
`y=0` equation and is already redundant.  A valid characteristic-five
proof must bring in another `b!=0` row.
