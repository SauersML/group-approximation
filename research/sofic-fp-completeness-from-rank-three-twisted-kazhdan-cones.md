---
rg: 2
id: sofic-fp-completeness-from-rank-three-twisted-kazhdan-cones
kind: route
title: A sofic rank-three twisted Kazhdan cone together with a machine switch would give sofic completeness for finite presentations
target: sofic-recognition-finite-presentations-is-pi2-complete
requires:
  - rank-three-finite-twisted-kazhdan-cone-is-sofic
  - twisted-kazhdan-cone-machine-switch
  - sofic-recognition-has-a-pi2-upper-bound
---

## Why sufficient

Assume `T_3` is sofic ([[rank-three-finite-twisted-kazhdan-cone-is-sofic]]).  Then
[[twisted-kazhdan-cone-machine-switch]] gives a computable family of finite presentations `X_e`.  `X_e` is sofic
for `e ∈ INF` and nonsofic for `e ∈ FIN`.  So `INF <=_m SOFIC_fp`, and with
[[sofic-recognition-has-a-pi2-upper-bound]], `SOFIC_fp` is `Pi^0_2`-complete.

## Status of the route

This is the only twisted-cone route that survives.  By
[[block-subpairs-make-twisted-kazhdan-cones-nonsofic]], every twisted-diagonal cone over a Theorem E pair of rank
`r ≥ 5` is nonsofic, and so is rank four with `q ∉ {2, 3, 5}`.  So a positive branch has to use a rank-three pair
(or rank four with `q ∈ {2, 3, 5}`).  If `T_3` is nonsofic, the route is dead.
[[divisor-level-subpairs-cannot-certify-rank-three-twisted-cone]] shows that the two natural families of
nonsofic certificates for `T_3` do not work.
