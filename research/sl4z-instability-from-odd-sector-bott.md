---
rg: 2
id: sl4z-instability-from-odd-sector-bott
kind: route
title: A nonzero odd-central-sector Bott index on the block-swap torus refutes stability of SL_4(Z)
target: sl4z-is-not-matricially-stable
requires:
  - sl4z-odd-central-sector-bott-is-realizable
  - sl4z-delocalized-bott-lives-in-odd-central-sector
---

## Why sufficient

1. By `sl4z-odd-central-sector-bott-is-realizable`, some asymptotic homomorphism `φ_n` of
   `SL_4(Z)` has `β_{+,−}(φ_n) ≠ 0` for infinitely many `n`.
2. Suppose genuine representations `π_n : SL_4(Z) → U(k_n)` satisfy `‖φ_n(y) − π_n(y)‖ → 0`
   for every `y`, in particular for `y ∈ F ∪ {M_1, M_2}`.
3. By part 1 of `sl4z-delocalized-bott-lives-in-odd-central-sector`,
   `β_{+,−}(φ_n) = β_{+,−}(π_n)` for large `n`, and `β_{+,−}(π_n) = 0`. This contradicts step 1.

So `φ_n` is not pointwise close to genuine representations, which is the target.
