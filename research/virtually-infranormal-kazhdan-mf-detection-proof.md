---
rg: 2
id: virtually-infranormal-kazhdan-mf-detection-proof
kind: route
title: Centralize the Kazhdan projection using compressors, then detect the corner by a finite average
target: virtually-infranormal-kazhdan-mf-detection
requires:
  - kazhdan-projection-finite-target-calculus
  - kazhdan-projection-is-norm-limit-of-finite-averages
  - matrix-corona-projection-ideal-and-corner-calculus
  - finite-index-op-hs-shadow-heredity
artifacts:
  - research/artifacts/infranormal-mf-detection-2026-09-13.md
---

Sections 2--5 give the proof. Finite projection comparison makes the
Kazhdan projection commute with every compressor, hence with their
generated subgroup `H`. For `H=G`, a nontrivial corona image of `K`
produces a nonzero complementary corner whose induced map kills `e_K`.
A probability average within `1/8` of `e_K` then has small operator norm
in that corner. Its normalized trace gives a fixed finite set of elements
of `K` with maximum normalized-HS displacement greater than one in the
corner models, contradicting `K <= S(G)`.

For finite-index `H`, shadow heredity gives `K <= S(H)`. The preceding
argument kills `K` in every MF image of `H`, hence in every MF image of
`G` by restriction. The converse is operator-norm domination of normalized
HS norm. No new formal verification is claimed.
