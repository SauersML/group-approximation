---
rg: 2
id: thompson-v-kernel-transfer-proof
kind: route
title: Push a failure into the corner of a prefix-permutation kernel idempotent along the tail-diagonal embedding
target: thompson-v-direct-finiteness-failures-transfer-into-kernel
requires: []
artifacts:
  - research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md
---

- `q` is an idempotent killed by `pi`. Its two factors are commuting idempotents supported on
  disjoint cylinders, and each factor evaluates to zero off its own cylinder, so the product
  evaluates to zero.
- `delta` acts by `g` on the tail after every depth-`k` prefix. So it is an injective homomorphism
  commuting with the pure prefix permutations `x, y`, and `delta(V)` meets `<x, y>` only in `1`.
- Hence `mu = delta_*(.) q` is unital onto `q`, multiplicative, injective by linear independence of
  the elements `delta(g) xi`, and killed by `pi`.
- The transfer of a strict pair is the standard padding by `1 - q`.

Artifact Section 3.
