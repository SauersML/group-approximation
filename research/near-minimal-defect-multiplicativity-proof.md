---
rg: 2
id: near-minimal-defect-multiplicativity-proof
kind: route
title: Bound the product from below by the range corner and from above by the kernel corner and a triangular rank count
target: near-minimal-defect-models-have-multiplicative-cylinder-defects
requires:
  - nested-two-root-defect-pieces-decay-geometrically-both-ways
  - leavitt-rank-models-kazhdan-fixed-ideals-are-global
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

Artifact Section 4, Proposition 4.1.

Put `P = D_(A_1)...D_(A_k)` and `B = A_(k+1)`.

1. **Lower bound.** The range corner gives `f(k+1) >= c_* f(k) >= delta f(k)/(1+eps)`.
2. **Kernel corner.** The right annihilator `K` of `P` has rank `1 - f(k)` and is invariant under
   `sigma(iota_B(R^x))`. Its corner model is fixed-point-free by globality, so
   `rk(D_(B1000) k) >= c_*(1 - f(k))`.
3. **Triangular count.** With `T = D_(B1000)` and `J = TM + K`:
   * `rk(TM) >= rk(TK) + rk(J) - rk(K)`;
   * `rk(J) - rk(K) = rk(PTM) = f(k+1)`, because `P` has right annihilator `K` and commutes with `T`;
   * so `delta >= c_*(1 - f(k)) + f(k+1)`.
4. **Upper bound.** Combining with `c_* >= delta/(1+eps)` gives `f(k+1) <= delta f(k) + eps delta`.
   Iterating with `delta <= 1/2` gives `|f(k) - delta^k| <= 2 eps delta`.
