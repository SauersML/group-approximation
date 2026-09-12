---
rg: 2
id: fpbs-random-horizontal-bridge-proof
kind: route
title: Compute the closest retained bridge over a separating free-tree edge
target: fpbs-reciprocal-shortest-route-obstruction
requires: []
artifacts:
  - research/artifacts/fpbs/fixed-price-percolation.md
  - research/artifacts/fpbs/scripts/replay.py
  - research/artifacts/fpbs/replay.json
---

Complete direct proof: Section 6, Proposition 4. The unique separating base-tree edge must be crossed. The nearest retained crossing height M has tail P(M>m)=(1-epsilon)^(2m+1), and the shortest path length is exactly 2M+1. Summing the geometric series gives the asserted formula and obstruction.
