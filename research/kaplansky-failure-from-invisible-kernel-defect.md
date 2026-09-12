---
rg: 2
id: kaplansky-failure-from-invisible-kernel-defect
kind: route
title: A one-sided inverse pair in the unitized evaluation kernel is a Kaplansky pair
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-evaluation-kernel-unitization-not-directly-finite
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

## Why sufficient

`K^+ = F_2 1 + K` is a unital subring of `F_2[R^x]` with the same identity. So a
pair `(1 + v)(1 + u) = 1 != (1 + u)(1 + v)` in `K^+` is a pair in `F_2[R^x]` with
`b a = 1 != a b`, and that is what the target asks for.

This is the invisible normal form of
`leavitt-inverse-defects-are-visible-or-invisible`. The visible form reaches the
same target through `leavitt-direct-finiteness-failure-from-left-invertible-lift`.
By that theorem the two routes are exhaustive: every witness of the target is a
group-element translate of a witness to one of their prerequisites.

The gk-kdf-lift lane landed an identical route. It was merged into this one on
2026-09-12.

*Verified independently by `gk-vf-linear` (2026-09-12): `F_2 1 + ker pi` is a unital subring with the same identity. See Section 5 of the linear-family verification artifact.*
