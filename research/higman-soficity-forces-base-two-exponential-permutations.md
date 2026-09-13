---
rg: 2
id: higman-soficity-forces-base-two-exponential-permutations
kind: route
title: If Higman's group is sofic it is its own nontrivial sofic quotient, so the base-two permutations exist
target: order-four-exponential-permutations-exist-for-base-two
requires:
  - higman-group-is-sofic
  - base-two-exponential-permutations-iff-sofic-higman-quotient
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

## Why sufficient

`H4` is nontrivial. If it is sofic, the identity quotient witnesses item 2 of
`base-two-exponential-permutations-iff-sofic-higman-quotient`, which gives item
1, the target.

This is the Helfgott--Juschenko Theorem 2 (`thm:jut`, arXiv:1512.02135) for
`m = 2`. The route records it so that the frontier hole `higman-group-is-sofic`
feeds its known necessary condition.
