---
rg: 2
id: leavitt-area-ten-odd-core-exclusion-proof
kind: route
title: Restore every loop and digon gadget over the complete six-vertex ribbon atlas
target: leavitt-area-ten-odd-residue-core-does-not-exist
requires:
  - leavitt-area-ten-long-residue-is-one-odd-budget
---

Contract the unique digon.  Distributing its two face incidences leaves one
of `(1,4,4,4,4,7)`, `(1,2,4,4,4,9)`, or
`(1,2,2,4,4,11)`.  The first has a monogon, so deleting its loop-lollipop
gadget gives a six-vertex cubic ribbon map.  The latter two have a digon, so
contracting it does the same.

Enumerate the 16 connected cubic multigraph types on six vertices and every
local rotation, obtaining 231 planar ribbon representatives and the complete
25 face partitions.  Restore a loop-lollipop and a digon on every edge.
None of the three required eight-vertex partitions occurs.  Therefore the
odd area-ten core is topologically impossible.
