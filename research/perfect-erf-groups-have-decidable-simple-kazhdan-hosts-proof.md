---
rg: 2
id: perfect-erf-groups-have-decidable-simple-kazhdan-hosts-proof
kind: route
title: Take the Toeplitz envelope of the overgroup and read its word problem off the degree formula
target: perfect-erf-groups-have-decidable-simple-kazhdan-hosts
requires: [rf-groups-embed-in-simple-kazhdan-lef-groups, residually-finite-group-toeplitz-elementary-groups-lef-kazhdan, crossed-product-el-word-problem-is-group-wp-plus-language, rf-toeplitz-subshift-has-computable-language, effectively-rf-groups-have-computable-chains]
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
---

Artifact §4, Theorem A.

1. **Chain.** `Δ` is effectively residually finite with solvable word problem, so
   `effectively-rf-groups-have-computable-chains` gives a computable chain `(Δ_m)` with decidable membership and
   computable finite quotients.
2. **Envelope.** Let `X_Δ` be the Toeplitz subshift of that chain and `G = EL_3(LC(X_Δ,F_2) ⋊ Δ)`. By
   `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`, `G` is infinite, finitely generated, simple,
   Kazhdan and LEF, with trivial centre over `F_2`.
3. **Embedding.** By `rf-groups-embed-in-simple-kazhdan-lef-groups`, `γ ↦ diag(u_γ,1,1)` is an injective
   homomorphism on `[Δ,Δ]`, through Whitehead's lemma and `diag([a,b],1,1) ∈ E_3`; restrict it to `Γ ≤ [Δ,Δ]`.
4. **Word problem.** By `crossed-product-el-word-problem-is-group-wp-plus-language`,
   `WP(G) ≡_T WP(Δ) ⊕ L(X_Δ)`. The first summand is decidable by hypothesis and the second by
   `rf-toeplitz-subshift-has-computable-language`.

For the corollary take `Δ = Γ`, which is legitimate exactly when `Γ = [Γ,Γ]`. For `SL_n(Z)`, `n ≥ 3`: it is
infinite, finitely presented, residually finite and perfect, so Rauzy's Fact 3 gives effective residual finiteness
and Mostowski's theorem the solvable word problem.

**Converse.** Fix words on the generators of `G` representing the images of a finite generating set of `Γ`. A word
on `Γ`'s generators maps to a computable word on `G`'s generators, trivial in `Γ` iff trivial in `G`, so
`WP(Γ) ≤_m WP(G)`. LEF passes to subgroups. ∎
