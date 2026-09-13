---
rg: 2
id: sylvester-rank-functions-are-submodular-on-stacked-rows-proof
kind: route
title: Shear the direct sum of two overlapping stacks into a triangular block and apply the triangular axiom once
target: sylvester-rank-functions-are-submodular-on-stacked-rows
requires: []
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

## Why sufficient

* **Part 1 (artifact Lemma 1.1).** `rho([A; B]) + rho([B; C])` is the rank of `diag([A; B], [B; C])`.
  - Multiply on the right by `[[I, 0], [I, I]]`.
  - Subtract the first `B` row block from the second.
  - Permute the rows to get `[[ [A; B; C], [0; 0; C] ], [0, B]]`.

  (S4) bounds the rank of that matrix below by `rho([A; B; C]) + rho(B)`.
* **Part 2 (artifact Lemma 1.3).**
  - `[M W; Y M W] = [I; Y (x) I] · M W` gives `M ≼ Y M`.
  - Invertible left factors and right translation (`(M v) W = M (v W)`) are block computations.
  - Transitivity is part 1 with `(A, B, C) = (M W, M' W, M'' W)`.
  - Stacking is part 1 with `(A, B, C) = (M_1 W, M W, M_2 W)`.
