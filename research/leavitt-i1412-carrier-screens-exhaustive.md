---
rg: 2
id: leavitt-i1412-carrier-screens-exhaustive
kind: claim
title: Both inverse 1;412 carrier minimum-block screens are exhaustive
artifacts:
  - research/artifacts/enumerate-l14-i1412-all-maximal.py
  - research/artifacts/enumerate-maximal-noncrossing-forests.py
  - research/leavitt-i1412-carrier-screens-exhaustive-proof.md
distinct_from:
  minimum-block-noncrossing-enumeration-is-not-exhaustive: that is the general counterexample; this is an exact word-specific exhaustive computation.
---

For the corrected inverse `1;412` carrier color words, every noncrossing
partition maximal under same-color coarsening has the globally minimum block
count.  The Eq3 word has exactly 9,894 maximal partitions, all with 15
blocks.  The Eq1 word has exactly 70,798 maximal partitions, all with 16
blocks.

Thus the coordinate-aware intersection of those two minimum-block screens
does exhaust the two carrier equations.  Boundary conjugacy remains a
separate all-maximal cyclic computation.
