---
rg: 2
id: deligne-cover-stable-finiteness-from-rank-projective-models
kind: route
title: Rank-approximate projective representations of Deligne's multiplier make every positive-characteristic group algebra of the cover stably finite
target: deligne-triple-cover-group-algebras-are-stably-finite
requires:
  - deligne-cocycle-has-rank-approximate-projective-representations
  - deligne-cover-linear-soficity-is-rank-projective-approximation
  - linear-sofic-group-algebra-is-stably-finite
  - deligne-triple-cover-ternary-group-algebras-are-stably-finite
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

1. **Characteristic `p != 3`.** Rank projective models give `F_p`-linear soficity of `E_3` (Theorem 2.1 of the
   artifact). An `F_p`-model is an `F`-model for every field `F` of characteristic `p`, so
   `linear-sofic-group-algebra-is-stably-finite` makes `F[E_3]` stably finite.
2. **Characteristic three.** Established directly.
