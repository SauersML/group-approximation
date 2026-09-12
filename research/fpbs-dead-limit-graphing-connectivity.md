---
rg: 2
id: fpbs-dead-limit-graphing-connectivity
kind: route
title: Transport cost through the limit of the near-cost-one graphings
target: fpbs-fixed-price-universal
requires: []
artifacts:
  - research/artifacts/fpbs/fixed-price-percolation.md
---

Dead: the attempt takes the limit of connected graphings whose cost tends to one and uses the limiting graphing to compare actions. Connectivity is not preserved. Under the common uniform-label coupling on F_r x Z the graphs H_epsilon converge to the disjoint vertical fibers, whose edges generate a proper subrelation, and the mean shortest replacement length grows like the reciprocal of the excess (fpbs-reciprocal-shortest-route-obstruction). A connected limit would need uniformly tight routes, which nonamenability forbids (fpbs-cost-one-routes-cannot-be-uniformly-tight). Costs approaching one along different graphings of one action are not different action costs.
