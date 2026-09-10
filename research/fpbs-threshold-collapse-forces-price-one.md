---
rg: 2
id: fpbs-threshold-collapse-forces-price-one
kind: route
title: Threshold equality collapses the maximal action cost to one
target: fpbs-non-fixed-price-one-has-nonuniqueness
requires:
  - fpbs-quantitative-cost-threshold-bound
artifacts:
  - research/artifacts/fpbs/fixed-price-percolation.md
---

By the quantitative bound, p_c=p_u implies C*<=1. Every free-action cost is at least one and at most C*, so all equal one. Contraposition gives the claim. The standard transitive Bernoulli phase theorem interprets p_c<p_u as infinitely many infinite clusters throughout the intermediate interval. See Sections 2 and 5 and Lyons, arXiv:1109.5418v1.
