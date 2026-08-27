---
rg: 2
id: leavitt-degree3-direct-pivot-screen-is-empty
kind: claim
title: No degree-three full-packet layout kills the center through one unary pivot
artifacts:
  - research/leavitt-degree3-direct-pivot-screen-proof.md
  - research/artifacts/search-leavitt-degree3-postpivot.py
  - research/artifacts/search-leavitt-degree3-postpivot.sbatch
distinct_from:
  leavitt-padded-center-template-has-no-degree2-packet: that treats the shortest one-unary degree-two topology; this treats all two-unary degree-three topologies but only direct substitution through either pivot separately.
---

There are exactly eleven degree-three, length-eleven cyclic sign topologies
whose Reidemeister--Schreier orbit valences are `(1,1,9)`.  Across every
placement of the full Leavitt coefficient packet with four identity slots,
solving either unary orbit and substituting it into the nine-valent orbit never
produces the central involution `[c_i,d_i]` in a coefficient copy.

This leaves a sharply different possibility: after one unary pivot, the second
unary relator may participate nontrivially in the normal-closure consequence
that kills the center.  The claim does not exclude that two-relator mechanism.
