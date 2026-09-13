---
rg: 2
id: raag-virtual-fn-kernel-conjecture-via-sigma-invariants
kind: route
title: Zaremsky's conjecture 1.19 from nonempty Sigma^n forcing (n-1)-connectivity of L, then Bestvina--Brady
target: raag-virtual-fn-kernel-implies-raag-fn-kernel
requires:
  - raag-finite-index-sigma-m-forces-connected-flag-complex
  - bestvina-brady-kernel-finiteness-theorem
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part2.md
---

Let `H ≤ A_L` have finite index and `ψ: H → Z` be an epimorphism whose kernel is of type `F_n`.
`H` is of type `F`. By the Bieri--Renz criterion `[ψ] ∈ Σ^n(H)`, so `Σ^n(H) ≠ ∅`. By
`raag-finite-index-sigma-m-forces-connected-flag-complex`, `L` is `(n−1)`-connected. By
`bestvina-brady-kernel-finiteness-theorem`, `BB_L` is of type `F_n`, so `A_L` maps onto `Z` with a
kernel of type `F_n`. Artifact part 2, Corollary 8.

The same argument with `FP_n(R)` and `Σ^n(H; R)` gives the homological version over every
commutative ring (Corollary 9).
