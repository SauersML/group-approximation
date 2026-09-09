---
rg: 2
id: tail-heights-prove-two-sided-natural-injections
kind: route
title: Remove positive tail heights and contradict adjacent periodic coefficients
target: two-sided-deletion-corrections-pass-natural-kernel-test
requires: []
artifacts:
  - research/artifacts/kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md
---

Both H_z have injective creator parts. On a tail class with no
eventually periodic sequences, assign an integer height by prefix
length minus deletion length relative to a fixed tail. This is
well-defined precisely because the class is not eventually
periodic. The image one level above a finite support's maximum
height consists only of its creator contribution, which cannot
vanish.

For an eventually periodic class, use minimal depth to its finite
periodic core. The same creator argument eliminates every positive
depth. Wrong-prefix outputs from the remaining core constrain
each two-coordinate coefficient to one scalar c_i. The explicit
core equations force nonzero c_j to have preceding bits 10 for
z=omega and 01 for z=omega^2. They also force c_j=c_(j-1),
whose required preceding bits contradict that condition.

All coefficients therefore vanish. The argument applies to
primitive periods one and two as well, without identifying
different actual binary sequences.

For the exterior map, the artifact separately computes the
highest creator layer and identifies its nonzero symmetric-tensor
kernel. Natural injectivity therefore does not justify repeating
the same maximum-height argument on the full exterior source.
