---
rg: 2
id: finite-syndrome-kernel-cone-proof
kind: route
title: Restrict positive effects to the forced ranges and separate a closed cone if identity is absent
target: finite-syndrome-cost-is-a-kernel-support-cone-test
requires: [local-syndrome-synthesis-has-an-exact-sdp-test]
artifacts:
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
---

Theorems 1 and 2 of the artifact prove the statement in full. Finite
domination forces each effect into every charged range; conversely, a
positive contraction in the range of a fixed positive matrix is dominated
by the inverse of its least positive eigenvalue. Closure of the support
cone follows from bounded traces of its positive summands. If identity
is outside, the nearest-point separator can be shifted strictly negative
on every permitted support and dominated by sufficiently large sums of
kernel projections. These projections have zero energy trace pairing,
giving the claimed complete alternative.
