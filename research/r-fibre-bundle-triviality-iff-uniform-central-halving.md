---
rg: 2
id: r-fibre-bundle-triviality-iff-uniform-central-halving
kind: claim
title: A hyperfinite W*-bundle is trivial iff it has uniformly central approximate halving projections
distinct_from:
  r-fibre-w-star-bundle-finite-dim-base-is-trivial: that is Ozawa's Corollary 16, triviality over finite-dimensional bases; this is his Theorem 15, the criterion over every compact metrizable base that the corollary and its infinite-dimensional extensions consume.
  bauer-uniform-gamma-iff-trivial-tracial-bundle: that is the dictionary between uniform property Gamma of an algebra and triviality of its strict closure; this is the abstract bundle criterion with no C*-algebra.
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

Let `M` be a strictly separable continuous W*-bundle over a compact metrizable
`K` with `π_λ(M) ≅ R` for every `λ`.  Then `M ≅ C_σ(K,R)` if and only if there
is a sequence `(p_n)` in `M` such that:
- `0 ≤ p_n ≤ 1`;
- `‖p_n − p_n²‖_{2,u} → 0`;
- `‖E(p_n) − 1/2‖ → 0`;
- `‖[p_n, a]‖_{2,u} → 0` for every `a ∈ M`.

This is Ozawa, arXiv:1304.3523, Theorem 15 (i) ⟺ (ii).
