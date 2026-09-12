---
rg: 2
id: kaplansky-failure-from-invisible-kernel-defect
kind: route
title: A one-sided inverse pair in the unitized evaluation kernel is a Kaplansky pair
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-evaluation-kernel-unitization-not-directly-finite
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

## Why sufficient

`K^+ = F_2 1 + K` is a unital subring of `F_2[R^x]` with the same identity. A
pair `(1 + v)(1 + u) = 1 != (1 + u)(1 + v)` in it is literally a pair in
`F_2[R^x]` with `b a = 1 != a b`, which is what the target asks for.

This is the invisible normal form of
`leavitt-inverse-defects-are-visible-or-invisible`. The visible form reaches the
same target through `leavitt-direct-finiteness-failure-from-left-invertible-lift`.
By that theorem these two routes are exhaustive: every witness of the target
is a group-element translate of a witness to one of their prerequisites.
