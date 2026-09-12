---
rg: 2
id: fpbs-traffic-defect-is-total-variation-loss-proof
kind: route
title: Rewrite the clipping gap through the Jordan decomposition of the signed traffic measure
target: fpbs-traffic-defect-is-total-variation-loss
requires: []
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression-checks.json
  - research/artifacts/fpbs/scripts/verify_reuse_compression.py
---

Section 3 of the artifact, with the finite checks recorded in the results file. Boundedness of the traffic of a fixed finite plan makes every total variation finite; the elementary min identity converts the clipping gap into the loss of total variation under pushforward, and conditional expectation is an L1 contraction. This is a supplied deduction with a finite exact-arithmetic check, not external validation.
