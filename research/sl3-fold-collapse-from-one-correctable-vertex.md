---
rg: 2
id: sl3-fold-collapse-from-one-correctable-vertex
kind: route
title: Anchor one double vertex, correct the other, and apply projective folding
target: sl3-regular-arithmetic-double-fold-mark-collapse
requires:
  - sl3-canonical-double-has-a-correctable-vertex
  - sl3-double-one-near-vertex-forces-joint-near-exactness
  - sl3-arithmetic-double-near-exact-vertices-fold-projectively
---

For each canonical double microstate, choose the correctable vertex supplied
by the first prerequisite.  The one-vertex anchor theorem moves the other
vertex to the same exact representation with normalized-HS error tending to
zero.  The joint near-exact folding theorem then gives trace modulus tending
to one for the fold-kernel mark.  This is exactly the target claim.

