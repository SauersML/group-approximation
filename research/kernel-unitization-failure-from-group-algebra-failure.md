---
rg: 2
id: kernel-unitization-failure-from-group-algebra-failure
kind: route
title: Any failure of direct finiteness of the Leavitt unit group algebra gives an invisible failure
target: leavitt-evaluation-kernel-unitization-not-directly-finite
requires:
  - leavitt-unit-group-algebra-not-directly-finite
  - leavitt-kaplansky-failures-have-invisible-witnesses
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

A one-sided pair `b a = 1 != a b` in `F_2[R^x]` is supplied by the first prerequisite.
The second converts it to `Phi(b) Phi(a) = 1 != Phi(a) Phi(b)` with both factors in
`1 + K`. That is exactly a witness `u = Phi(a) - 1`, `v = Phi(b) - 1` for the target.

This route and `kaplansky-failure-from-invisible-kernel-defect` form an intended
equivalence cycle between the invisible problem and the Kaplansky failure for `R^x`.
Neither route establishes anything alone.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 16 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
