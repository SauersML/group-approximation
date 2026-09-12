---
rg: 2
id: fixed-field-plane-point-robustness-proof
kind: route
title: Read the d-over-q term and compute tensor Reed--Solomon distance
target: fixed-field-plane-point-loses-uniform-low-degree-robustness
requires: []
artifacts:
  - research/artifacts/quantum-low-degree-occurrence-audit-2026-08-21.md
---

Theorem 3.2 of arXiv:1801.03821 explicitly includes `poly(d/q)` in the
robustness and sets `d=hm`.  Independently, minimum-weight codewords in the
individual-degree tensor evaluation code are products of `m` univariate
minimum-weight words, giving relative distance `((q-h)/q)^m`.  Both
calculations rule out the fixed-field specialization recorded in the target.
