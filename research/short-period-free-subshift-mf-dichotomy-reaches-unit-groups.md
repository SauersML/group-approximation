---
rg: 2
id: short-period-free-subshift-mf-dichotomy-reaches-unit-groups
kind: claim
title: Without short periodic orbits the exact subshift MF and LEF criterion reaches rank two and the unit group
root: true
distinct_from:
  subshift-elementary-mf-iff-word-edges-lie-on-cycles: that detects failure in outer rank at least four; this uses return corners in the same ring to reach rank two without fixed points and rank one for units without periods below four.
artifacts:
  - research/artifacts/pestov91-return-towers-lower-mf-rank-2026-09-13.md
---

Let `R_X=LC(X,F_q) semidirect Z`. Suppose `T^j` has no fixed point
for `1<=j<k`. For `nk>=4`, the word-graph cycle condition is equivalent
to LEF and to operator MF of `GL_n(R_X)`. For `n>=2`, the same holds
for `EL_n(R_X)`.

In particular rank two suffices when `X` has no fixed points. If `X`
has no points of periods one, two or three, its unit group is MF
exactly when it is LEF, exactly when the ring is directly finite.
Thus this unit-group criterion holds for every aperiodic subshift.
Failure supplies a nonzero return-corner defect `d`, with invisible
root `e_12(d)` in the elementary cases and invisible unit `1+d u^{-1}`
in the unit-group case.
