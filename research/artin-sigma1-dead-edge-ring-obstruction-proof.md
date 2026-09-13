---
rg: 2
id: artin-sigma1-dead-edge-ring-obstruction-proof
kind: route
title: Prove the dead-edge ring obstruction with twisted Laurent homology and Fox calculus
target: artin-sigma1-dead-edge-ring-obstruction
requires:
  - artin-sigma1-living-subgraph-bounds
artifacts:
  - research/artifacts/zp-artin-sigma1-dead-edge-rings-2026-09-13.md
---

The derivation is in the artifact.

- §2, Lemma A: for a finitely presented group with finitely generated `ker χ`,
  `H_1(G; R((t))) = H_1(G; R((t^{-1}))) = 0` for every ring `R` and every
  `ρ : G -> R^×`.
- §3: the Fox derivatives of the relator `(uv)^k (vu)^{-k}` are
  `(1 - X_v) S_k(X_u X_v)` and `(X_u - 1) S_k(X_v X_u)`.
- §4, Theorem C: the functional `Φ` shows `H_1(A_Γ; R((t))) ↠ R((t)) != 0`.

The symmetry `Σ^1(A_Γ) = -Σ^1(A_Γ)` and the Bieri–Renz criterion (finite generation
of `ker χ` iff `±[χ] ∈ Σ^1`) are the imported inputs, recorded in
`artin-sigma1-living-subgraph-bounds`.
