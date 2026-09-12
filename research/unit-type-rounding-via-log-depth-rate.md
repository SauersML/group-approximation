---
rg: 2
id: unit-type-rounding-via-log-depth-rate
kind: route
title: Vertex rounding with a log-depth rate kills all non-unit mass and gives unit-type rounding
target: theorem-e-vertex-rounds-to-unit-type-representations
requires:
  - vertex-rounding-with-log-depth-rate
  - nonunit-root-mass-log-depth-scale-bound
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

- `vertex-rounding-with-log-depth-rate` supplies (H1) with `δ_n^2 log(1 + D(π_n)) -> 0` along `U`.
- Item 3 of `nonunit-root-mass-log-depth-scale-bound` then gives `τ(1 - P_n) -> 0`.
- Replace the non-unit constituents of `π_n` by the trivial representation. This changes `π_n` on
  generators by at most `2·τ(1 - P_n)^(1/2) -> 0` in normalized 2-norm, so it is still a rounding, now of
  unit type. That is `theorem-e-vertex-rounds-to-unit-type-representations`.
