---
rg: 2
id: compiler-hyperlinear-from-host-coset-chain
kind: route
title: Apply the host-coset reduction and then permutation-to-unitary approximation
target: mf-compiler-positive-branch-is-hyperlinear
requires:
  - mf-compiler-is-uniform-in-finite-seeds
  - compiler-higman-coset-chain-is-sofic
  - higman-host-coset-soficity-makes-compiler-rope-sofic
  - sofic-implies-hyperlinear
artifacts:
  - research/artifacts/liu-new-frontiers-2026-09-20.md
---

Fix a seed code d and e in INF. The uniform compiler premise defines
the actual host and rope. The host-chain premise supplies exactly the
separating-chain version of (HQ) permitted by the host theorem. That
theorem applies pointwise to these construction data and gives a sofic
model of the whole twisted rope R_e(d), not just its vertex or edge
group. Sofic-to-hyperlinear conversion proves hyperlinearity for every
seed and every positive index. The quantified host
condition remains open. The older host-coset implication is an explicit
repository proof dependency; this short composition does not independently
certify that entire construction.

This route does not use MF => hyperlinear. Its relevance after Jihao Liu's
internality theorem is that a direct compatible-model proof survives
the refutation of that universal shortcut. No part of the host-coset
argument is attributed to Liu.
