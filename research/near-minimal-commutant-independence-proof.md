---
rg: 2
id: near-minimal-commutant-independence-proof
kind: route
title: Restrict the cylinder model to the range and the kernel of a commuting element and count ranks triangularly
target: near-minimal-defects-are-rank-independent-of-cylinder-commutants
requires:
  - leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
  - leavitt-rank-models-kazhdan-fixed-ideals-are-global
  - near-minimal-defect-models-have-multiplicative-cylinder-defects
artifacts:
  - research/artifacts/cylinder-commutant-independence-and-weyl-firewall-2026-09-12.md
---

Artifact Section 2, Theorem 2.1.

1. **Invariance.** If `X` commutes with `sigma(iota_A(R^x))`, then `XM` and the right annihilator `K`
   of `X` are invariant principal right ideals, of ranks `rk(X)` and `1 - rk(X)`.
2. **Range corner.** `e sigma(iota_A(.)) e` on `eM = XM` is a model of `R^x`. A fixed vector is fixed by
   `sigma(iota_A(R^x))`, hence global, hence zero. Its defect at a proper prefix is `D_(AP) e`, of rank
   `rk(D_(AP) X)`, so `rk(D_(AP) X) >= c_* rk(X)`.
3. **Kernel corner.** The same on `kMk` gives `rk(D_(AP) k) >= c_* (1 - rk(X))`.
4. **Triangular count.** With `T = D_(AP)` and `J = TM + K`, modularity gives
   `rk(TM) >= rk(TK) + rk(J) - rk(K)`, and `rk(J) - rk(K) = rk(XTM) = rk(TX)`. So
   `delta >= c_*(1 - rk(X)) + rk(D_(AP) X)`.
5. **Near-minimal estimate.** `delta <= (1+eps) c_*` turns the two bounds into
   `|rk(D_(AP) X) - delta rk(X)| <= eps delta`.

The descent artifact's Proposition 4.1 is the instance `X = D_(B_1)...D_(B_k)`; this route reruns its
argument for an arbitrary commuting `X`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 11.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
