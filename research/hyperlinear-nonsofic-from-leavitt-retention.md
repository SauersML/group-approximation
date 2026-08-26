---
rg: 2
id: hyperlinear-nonsofic-from-leavitt-retention
kind: route
title: Positive-rank intertwiner retention makes the nonsofic rank-four Leavitt group hyperlinear
target: hyperlinear-nonsofic-group
requires:
  - leavitt-presentation-double-positive-rank-retention
  - intertwiner-retention-makes-leavitt-quotient-hyperlinear
  - universal-leavitt-el4-nonsofic
---

`Q = EL_4(L_(F_2)(1,2))` is nonsofic (`universal-leavitt-el4-nonsofic`,
kernel-checked).  If the retained sector of
`leavitt-presentation-double-positive-rank-retention` exists, then
`intertwiner-retention-makes-leavitt-quotient-hyperlinear` makes `Q`
hyperlinear, and `Q` is the Pestov 3.4 separation.  This is the
presentation-double program of the 2026-08-26 attack notebook; its only open
input is the retention claim.
