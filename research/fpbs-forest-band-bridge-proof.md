---
rg: 2
id: fpbs-forest-band-bridge-proof
kind: route
title: Count subcritical cluster trees and band edges and one descending bridge per finite cluster
target: fpbs-quantitative-cost-threshold-bound
requires:
  - fpbs-bernoulli-maximal-cost
  - fpbs-finite-cluster-density-continuous
artifacts:
  - research/artifacts/fpbs/fixed-price-percolation.md
  - research/artifacts/fpbs/scripts/replay.py
  - research/artifacts/fpbs/replay.json
---

Complete proof: Section 4, Theorem 2. For q<p_c and a uniqueness parameter p, the Bernoulli orbit relation has a graphing of cost 1-kappa(q)+(d/2)(p-q)+kappa(p). Finite cluster trees preserve q-connectivity; band edges give precisely p-clusters; a height-decreasing bridge from each finite p-cluster connects to the unique infinite cluster. Mass transport gives the bridge intensity. Continuity handles both endpoints without assuming theta(p_c)=0 or uniqueness at p_u.
