---
rg: 2
id: formalizable-biorderable-pairs-affine-proof
kind: route
title: Invert formally, count degrees in the extreme variable, and invert a univariate polynomial
target: formalizable-binary-pairs-over-biorderable-groups-are-affine
requires:
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/binary-formalizability-refutation-2026-09-12.md
---

Section 1 of the artifact. The only imported step is the prerequisite:
- it applies with `n = 1` and `k = F_2`;
- the leading-term argument makes `F_2[G]` a domain, so `M_1(F_2[G])` is directly finite;
- so the formal left-inverse identity becomes two-sided.

Everything else is a degree count in one variable, over the domain `F_2[X_h : h in G]`, using that
the maximum of `V · W` in a bi-invariant order is attained only at `(max V, max W)`.
