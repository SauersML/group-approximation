---
rg: 2
id: fpbs-sharpness-russo-exponential-spike-proof
kind: route
title: Combine the sharpness lower bound with critical spectral decay and finite-volume Russo
target: fpbs-collapse-exponential-pivotal-spikes
requires:
  - fpbs-transitive-sharpness-linear-lower-bound
  - fpbs-uniqueness-spectral-atom-decomposition
  - fpbs-critical-walk-correlation
  - fpbs-integrated-pivotal-total-budget
artifacts:
  - research/artifacts/fpbs/spectral-spike.md
---

Section 6. Select epsilon_n=exp(-alpha*n); approximate the uniqueness correlation at finite radius; integrate the exact finite logarithmic derivative; use the mean-value theorem. The conclusion is a necessary condition under collapse, not a contradiction.
