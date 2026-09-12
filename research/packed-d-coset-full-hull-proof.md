---
rg: 2
id: packed-d-coset-full-hull-proof
kind: route
title: Pack double-coset representatives and count their cubic support
target: packed-d-coset-flip-has-full-bs-hull
requires: []
---

The target contains the proof.  Choose one right `D`-coset inside every
`B-D` double coset and let `Q` be the coordinate projection onto their
disjoint union.  Left `D`-invariance makes the involution and inversion rows
exact.  Each cubic is a product of three conjugate reflections, so its
defect has rank at most `3 rank(Q)` and squared Frobenius norm at most
`12 rank(Q)`.  The double-coset count gives `rank(Q)/|G|<=2/p`, whereas
`BE=G` makes the exact `B`-reducing hull equal to the full regular block.
