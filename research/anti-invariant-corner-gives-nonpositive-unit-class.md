---
rg: 2
id: anti-invariant-corner-gives-nonpositive-unit-class
kind: route
title: A corner solution makes the anti-central unit class nonpositive with k = 1
target: ternary-anti-central-unit-class-is-nonpositive
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **Positive class.** A solution gives an idempotent `f <= e_-` with `f ~ eps_-`, so
  `[e_-] - [eps_-]` is the class of the idempotent `e_- - f`.
- **Halving.** The split supplies `[eps_-] = 2[e_-]`.
- **Conclusion.** Then `[e_-] <= 0`, so `[eps_-] <= 0`.

Theorem A(a) of the artifact.
