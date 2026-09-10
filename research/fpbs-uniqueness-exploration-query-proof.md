---
rg: 2
id: fpbs-uniqueness-exploration-query-proof
kind: route
title: Compare critical transcripts and remove the bounded finite-endpoint contribution
target: fpbs-uniqueness-exploration-query-lower-bound
requires:
  - fpbs-adaptive-exploration-relative-entropy
  - fpbs-supercritical-finite-susceptibility
  - fpbs-critical-walk-correlation
  - fpbs-critical-cluster-stability-modulus
  - fpbs-bernoulli-lazy-covariance-bound
artifacts:
  - research/artifacts/fpbs/exploration-information.md
---

Sections 2-4 combine the critical rho^n connection bound with uniqueness
and positive association in the binary entropy inequality. Balanced search
uses at most 2d|C|+1 queries when an endpoint cluster is finite, giving a
uniform-in-n expected finite-endpoint cost from the imported tail theorem.
Bernoulli covariance makes the two-infinite-endpoint probability tend to
theta(q)^2. Division and the Taylor expansion of k(q,c) finish the bound.
