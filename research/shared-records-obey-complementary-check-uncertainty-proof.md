---
rg: 2
id: shared-records-obey-complementary-check-uncertainty-proof
kind: route
title: Proof of shared complementary measurement records require noncommutativity for small disagreement
target: shared-records-obey-complementary-check-uncertainty
requires: []
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

A and B square to identity, and (A+B)^2=2I+ZX tensor [Q_Z,Q_X].
The triangle inequality bounds ||A+B|| by sqrt(2+c); substitute in K
and rearrange, squaring only the nonnegative expression 2-4eta.
For commuting records the square is exactly 2I. Records predicting +1
and a top eigenvector of X+Z attain the floor. The Bell vector is fixed
by both Z tensor Z and X tensor X. Section 2 of the artifact supplies
the full operator proof and scope.

