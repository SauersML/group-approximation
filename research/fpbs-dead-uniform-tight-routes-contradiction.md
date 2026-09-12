---
rg: 2
id: fpbs-dead-uniform-tight-routes-contradiction
kind: route
title: Contradict collapsed thresholds using uniformly tight generator routes
target: fpbs-benjamini-schramm-universal
requires: []
artifacts:
  - research/artifacts/fpbs/fixed-price-percolation.md
  - research/artifacts/fpbs/routing-obstruction-continuation.md
---

Dead: assuming pc=pu, the cost-percolation construction produces invariant connected spanning subgraphs of edge intensity tending to one, and the attempt derives a contradiction by asserting that their generator replacement distances stay uniformly tight. That assertion is impossible for any such sequence on a nonamenable Cayley graph (fpbs-cost-one-routes-cannot-be-uniformly-tight), and the averaged tail at every fixed radius is bounded below by h/d (fpbs-quantitative-routing-tail-bound). Connectedness of each graphing gives a finite path but no uniform length bound. A percolation-specific estimate is needed instead.
