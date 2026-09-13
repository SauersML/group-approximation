---
rg: 2
id: lxi-negation-from-o2-multiplier-ideal
kind: route
title: A non-K1-injective unitization of an O_2-multiplier ideal refutes LXI
target: properly-infinite-unital-algebra-not-k1-injective-exists
requires: [o2-multiplier-ideal-with-non-k1-injective-unitization, o2-multiplier-extension-k1-injective-iff-unitization]
artifacts:
  - research/artifacts/lxi-o2-multiplier-reduction-2026-09-12.md
---

Given `I`, `S_1`, `S_2` and `u` as in the first required claim, let `A = C*(I, S_1, S_2) ⊆ M(I)`. By the
second required claim `A` is unital and properly infinite. A unitary of `Ĩ` is null in `A` only if it
is null in `Ĩ`, so `u ∉ U_0(A)`. Its class in `K_1(A)` is the image of `[u] = 0 ∈ K_1(I)`, hence zero.
So `A` is not K1-injective.
