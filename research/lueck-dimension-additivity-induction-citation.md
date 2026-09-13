---
rg: 2
id: lueck-dimension-additivity-induction-citation
kind: route
title: Import Theorems 1.11 and 1.18 of Lück's algebraic survey
target: lueck-dimension-additivity-cofinality-and-induction
requires: []
artifacts:
  - research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md
---

W. Lück, *L²-Invariants from the Algebraic Point of View*, arXiv:math/0310489. Read from the
PDF text on MSI on 2026-09-12 (artifact Section 6).
- **Theorem 1.11 (iii)**: "There exists precisely one dimension function dim_N(G):
  {N(G)-modules} → [0,∞] which satisfies: (a) Extension Property [...] (b) Additivity [...]
  (c) Cofinality: Let {Mi | i ∈ I} be a cofinal system of submodules of M [...] Then
  dim(M) = sup{dim(Mi) | i ∈ I}". The survey cites its proof to Lück's book, Theorem 6.7.
- **Theorem 1.18 (Induction and dimension)**: "Let i: H → G be an injective group
  homomorphism. Then (i) Induction with N(i): N(H) → N(G) is a faithfully flat functor [...]
  (ii) For any N(H)-module M we have: dim_N(H)(M) = dim_N(G)(i∗M)."

The two consequences in the claim are one-line derivations: countable sums are cofinal unions
of finite sums, and `N(G) ⊗_(N(H)) −` commutes with homology by flatness.
