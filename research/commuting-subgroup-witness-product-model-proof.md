---
rg: 2
id: commuting-subgroup-witness-product-model-proof
kind: route
title: Tensor the regular direct-limit model of a locally finite cylinder group with any rank model of a commuting subgroup; ranks multiply, so commuting witnesses keep the defect proportional
target: commuting-subgroup-witnesses-cannot-distort-defect-ranges
requires: []
artifacts:
  - research/artifacts/commutant-distortion-product-firewall-2026-09-12.md
---

Artifact Theorem 2.1 and Corollary 2.2.

1. **Commuting factors.** Units supported on `U` and on `U^c` satisfy `(g-1)(h-1) = 0 = (h-1)(g-1)` because
   `p_U p_(U^c) = 0`, so they commute and meet trivially.
2. **Model of `L`.** The left regular representations of an exhaustion `H_n` of `L` define `sigma_L` along an
   ultrafilter. Relations hold eventually, and ranks on finite-subgroup algebras are regular.
3. **Tensor ultraproduct.** Along the product ultrafilter `U (x) V`, `sigma(g,h) = [lambda_n(g) (x) rho_i(h)]` is a
   homomorphism of `L x Lambda`, and normalized ranks of elementary tensors multiply.
4. **Defect and witnesses.** `<x, y> = D_8` gives `rk(T) = 3/8`, and `T (1 (x) rho(beta))` has rank
   `(3/8) rk(rho(beta))`.
5. **Fixed points.** Vectors fixed by `lambda_n(H_m) (x) 1` have normalized dimension at most `1/|H_m|`, which tends
   to `0`, so the model is fixed-point-free.
6. **Escapes.** `b` and `x^A_12(s_0) x^A_21(1)` generate infinite cyclic groups, which carry rank models.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 25.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS. Scope: the firewall content requires a rank model rho that separates Lambda, as in Corollary 2.2.*
