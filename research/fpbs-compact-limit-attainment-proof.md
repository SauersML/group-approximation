---
rg: 2
id: fpbs-compact-limit-attainment-proof
kind: route
title: Uniformly tight routes would make a cost-one compact limit stay connected
target: fpbs-cost-one-routes-cannot-be-uniformly-tight
requires:
  - fpbs-attained-cost-one-amenable
artifacts:
  - research/artifacts/fpbs/fixed-price-percolation.md
---

Complete proof: Section 7, Proposition 5. Compactness of edge configurations gives an invariant limit with mean degree two. Bounded-length connection events are cylinders; uniform tightness preserves almost-sure connection for every generator and hence full connectivity. Multiplying by a free Bernoulli action produces a free action with an attained cost-one graphing, contradicting the amenability theorem.
