---
rg: 2
id: bernoulli-coset-shift-factors-trivial-proof
kind: route
title: Restrict the Bernoulli shift to the infinite stabilizer and use mixing
target: bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial
requires: []
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Section 3 of the artifact.

1. **Invariance.** For `k in K`, `f(k.x) = (k.F(x))(K) = F(x)(k^-1 K) = f(x)`.
2. **Mixing.** Take Borel sets `S, S'` in `A^G` that depend on finite coordinate sets `P, Q`. Then
   `k.S` depends on `kP`, which misses `Q` for all but finitely many `k`, and there
   `mu(k.S ∩ S') = mu(S) mu(S')`. Approximating Borel sets by cylinders gives mixing of `K`, hence
   ergodicity, so `f` is almost everywhere a constant `b`.
3. **Every coset.** For `g in G`, `F(x)(gK) = F(g^-1.x)(K) = f(g^-1.x) = b` for almost every `x`,
   since `g^-1` preserves `mu`. There are countably many cosets, so `F(x) = b` almost everywhere.
