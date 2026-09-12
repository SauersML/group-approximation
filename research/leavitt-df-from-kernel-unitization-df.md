---
rg: 2
id: leavitt-df-from-kernel-unitization-df
kind: route
title: Direct finiteness of the unitized evaluation kernel gives direct finiteness of the whole group algebra
target: leavitt-unit-group-algebra-is-directly-finite
requires:
  - leavitt-evaluation-kernel-unitization-directly-finite
  - leavitt-kaplansky-failures-have-invisible-witnesses
artifacts:
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

Suppose `F_2[R^x]` had a one-sided pair. The second prerequisite converts it into a
one-sided pair in `K^+`, contradicting the first. So `F_2[R^x]` is directly finite.

This replaces the need for both negations in
`leavitt-direct-finiteness-from-both-lifting-problems-failing`. Excluding invisible pairs
already excludes visible ones.
