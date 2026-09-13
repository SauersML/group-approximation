---
rg: 2
id: stw99-lxi-from-uniform-unstable-length-bound
kind: route
title: A uniform unstable exponential-length bound implies LXI
target: stw99-problem-lxi-properly-infinite-k1-injective
requires: [properly-infinite-unstable-length-uniformly-bounded]
artifacts:
  - research/artifacts/lxi-uniform-unitary-length-reformulation-2026-09-12.md
---

Let `A` be unital and properly infinite, and let `[u] = 0` in `K_1(A)`. Apply BRR Lemma 2.4(ii) in
`M_2(A)` to `diag(u,1)` with `p = diag(1,0)`. Here `p` commutes with `diag(u,1)`, `p` and `1-p` are
properly infinite and full, and the `K_1` class is zero. So `diag(u,1) ∈ U_0(M_2(A))` and its exponential
length `L` is finite. The required claim gives `cel_A(u) ≤ F(L) < ∞`, so `u ∈ U_0(A)`. Artifact
Theorem B, 3 => 1.
