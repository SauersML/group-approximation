---
rg: 2
id: stw99-problem-xcviii-free-isomorphism
kind: claim
title: Distinguish or identify finite reduced free powers of Jiang-Su and the interval (STW Problem XCVIII)
root: true
distinct_from:
  hirshberg-phillips-infinite-free-products-isomorphic: that established theorem settles the infinite-power case; this problem is the surviving finite-k case, where the infinite-product techniques break.
artifacts:
  - research/artifacts/stw99-final-band-cluster-2026-08-30.md
---

**Problem XCVIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(their "correct C*-version of the free group factor problem").
Determine which of `(Z, τ)^{*k}` and `(C([0,1]), τ_Leb)^{*ℓ}`
(`k, ℓ ≥ 2`) are isomorphic.  Germain's K-theory computations make all
the K-data agree (unlike `C*_r(F_n)`, where `K_1` separates), and the
semicircular-system free products now have strict comparison (HEKR).

## Attempts

* The infinite case is CLOSED
  (`hirshberg-phillips-infinite-free-products-isomorphic`), so any
  distinguishing invariant for finite `k` must die at `∞`: this rules
  out every stable/absorbing invariant and points at free-probability
  quantities with linear-in-`k` behaviour — free entropy dimension of
  canonical generators is THE candidate (its von Neumann analogue is
  what the free group factor problem lacks; here the C*-setting
  offers topological free entropy dimension, and `Z^{*k}` vs
  `C[0,1]^{*k}` have different natural generator profiles: `k`
  semicircular-like vs `k` diffuse-commutative families).  The
  recorded sharp subproblem: is topological free entropy dimension
  (or a strict-comparison-compatible variant) an isomorphism
  invariant that distinguishes `Z^{*2}` from `C[0,1]^{*2}`?  With
  HEKR comparison + selflessness the model-theoretic route
  (Kunnawalkam Elayavalli--Schafhauser ultrapower separation
  technology) also opens: separate them by a first-order tracial
  property; nothing separating is currently known, and the identity
  `Z^{*∞} ≅ C[0,1]^{*∞}` cautions that they may simply be isomorphic
  for all `k`.
