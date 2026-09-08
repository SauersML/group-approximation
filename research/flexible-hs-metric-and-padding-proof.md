---
rg: 2
id: flexible-hs-metric-and-padding-proof
kind: route
title: Prove the relative Hilbert metric and compare zero padding with trivial summands
target: flexible-hs-metric-controls-words-and-padding
requires: []
artifacts:
  - research/artifacts/flexible-hs-metric-and-padding.md
  - experiments/flexible_hs_metric_audit.py
  - research/artifacts/flexible-hs-metric-replay.json
---

Sections 1--4 of the artifact give the complete argument. Hilbert-space
inversion proves the triangle inequality for `||x-y||/max(||x||,||y||)`;
zero-extended unitaries have Hilbert norm equal to the square root of their
dimension. Telescoping nonempty words and applying that metric triangle
proves the local-defect estimate in either dimension ordering. The empty
word is handled by the dimension charge, rather than a length-zero bound.

The exact compression identity (6) proves the dimension charge and leakage
estimate. Replacing a smaller exact comparison by its direct sum with
trivial representations costs at most twice the original distance.
The three branches of (12) compute both distance infima over all positive
dimensions and prove sharpness. No compactness, finite-size extrapolation,
or missing stability assumption is used for this claim.
