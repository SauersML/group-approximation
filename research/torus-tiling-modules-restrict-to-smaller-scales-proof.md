---
rg: 2
id: torus-tiling-modules-restrict-to-smaller-scales-proof
kind: route
title: Illegal small patterns are sums of illegal large patterns, by the partition of unity at each site
target: torus-tiling-modules-restrict-to-smaller-scales
requires: []
artifacts:
  - research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md
---

Artifact §2.

- (T1) is the same relation at both scales, and (T2) at distance `2D'` is part of (T2) at distance `2D`.
- (T3) at scale `D'`: let `π ∉ L_(B_(D'))(Ω)` be placed at `t`. Insert `sum_a e_a(t+h) = 1` for every
  `h ∈ B_D \ B_(D')`. The product over `B_(D')` becomes the sum, over all extensions `π̃` of `π` to `B_D`, of
  `prod_(h ∈ B_D) e_(π̃(h))(t+h)`, whose factors commute by (T2) at scale `D`.
- Each `π̃` restricts to the illegal `π`, so `π̃ ∉ L_(B_D)(Ω)`. (T3) at scale `D` kills every term. ∎
