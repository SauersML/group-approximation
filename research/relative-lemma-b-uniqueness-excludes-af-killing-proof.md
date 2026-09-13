---
rg: 2
id: relative-lemma-b-uniqueness-excludes-af-killing-proof
kind: route
title: A trace normalised at a projection outside the finiteness ideal is a second annihilating trace
target: relative-lemma-b-uniqueness-excludes-af-killing
requires: [af-killing-embeddings-force-projection-annihilating-traces, stably-finite-projections-carry-annihilating-traces]
artifacts:
  - research/artifacts/bk-af-killing-projection-traces-2026-09-13.md
---

Corollary C in §3 of the artifact.

1. Some diagonal entry of `P` lies outside `I`, because a positive matrix whose
   diagonal lies in `I` has all its entries in `I`.  So `(Tr ⊗ τ)(P) = ∞` by
   hypothesis (2).
2. Theorem A (for a map with `φ(P) ≠ 0`) or Proposition B (for the boundary of a
   stably finite exact extension) gives `σ` annihilating `G` on its finiteness
   ideal with `σ(P) = 1`.
3. `σ` is finite and nonzero at `P` while every positive multiple of `τ` is
   infinite there, contradicting (3′).
