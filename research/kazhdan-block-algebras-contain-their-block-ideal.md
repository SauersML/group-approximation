---
rg: 2
id: kazhdan-block-algebras-contain-their-block-ideal
kind: claim
title: A Kazhdan block algebra contains the norm-null sum of its blocks, and its corona has no finite-dimensional representation
distinct_from:
  kazhdan-fd-block-representation-algebras-are-not-exact: that proves the same block algebra is not exact, through a Kazhdan projection in a spatial tensor product; this proves the block ideal lies inside the algebra itself, by Fell isolation of finite-dimensional representations, and reduces quasitrace linearity to the corona.
  stw01-extensions-preserve-qt-linearity: that is the general extension permanence theorem for quasitrace linearity; this supplies the specific ideal to which it is applied for Kazhdan block algebras.
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

**ESTABLISHED (derivation `kazhdan-block-ideal-fell-isolation-proof`).** Setting:
- `G` is a discrete group with property (T);
- `σ_j` (`j ∈ N`) are pairwise inequivalent finite-dimensional irreducible unitary
  representations, with `n_j = dim σ_j`;
- `ρ = ⊕_j σ_j`, and `B = C*_ρ(G) ⊂ ∏_j M_{n_j}`.

Then:
1. `B` contains the block ideal `I = ⊕_j M_{n_j}` of norm-null sequences.
2. The corona `B/I` has no finite-dimensional irreducible representation.
3. Every bounded 2-quasitrace on `B` is a trace iff every bounded 2-quasitrace on
   `B/I` is a trace.

**Proof idea.**
- A finite-dimensional irreducible `σ` weakly contained in a representation `π` of
  a Kazhdan group is contained in `π`: `π ⊗ σ̄` almost has invariant vectors, and an
  invariant vector is an intertwiner.
- So each `σ_j` is an open point of the spectrum of `B`. The corresponding ideal is
  the block `M_{n_j}`.
- Item 3 follows from `stw01-extensions-preserve-qt-linearity`, because quasitraces
  on `I` are traces: split along the central projections `⊕_{j ≤ m} 1_{n_j}`.

**Instance.** Ozawa's block algebra `D = C*(⊕_k π_k(SL(3,Z)))` contains
`⊕_k M_{p_k² + p_k}`.

Credit: isolation of finite-dimensional representations of Kazhdan groups is
classical (Wang; Bekka–de la Harpe–Valette). No novelty is claimed. Proofs are in
§1 of the artifact.
