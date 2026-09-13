---
rg: 2
id: left-orderable-free-product-normal-rank-citation
kind: route
title: Import Chen--Lodha Theorem B on free products of left-orderable groups
target: left-orderable-free-products-have-normal-rank-above-one
requires: []
---

Citation import, not reproved. Source: Chen–Lodha, *The Wiegold problem and free
products of left-orderable groups*, arXiv:2510.26073 v2 (1 December 2025), file
`wiegold.tex`, fetched as the arXiv e-print on MSI on 2026-09-13. TeX macros are
stripped from the quotes.

- **l.198–200, Theorem B** (`thmA: main`): "Any free product G=A⋆B of nontrivial
  left-orderable groups A and B has normal rank greater than 1. More precisely,
  for any w∈G not conjugate into A, the natural map A↪A⋆B induces an injection
  A↪(A⋆B)/⟪w⟫."
- **l.204:** "We remark that the same estimate of normal rank holds for free
  products of groups, where each free factor admits a nontrivial left-orderable
  quotient."
- **l.231:** "Actually, if A is torsion-free, the Levin conjecture [Levin] asserts
  that the result holds with the weaker assumption that w is not conjugate into
  A. Theorem B confirms this for A left-orderable since B=Z."
- **l.1446–1468, proof of Theorem B.**
  - The case where `w` is conjugate into `B` is disposed of directly: "This is
    obvious if w is conjugate to some b∈B since (A⋆B)/⟪w⟫=A⋆(B/⟪b⟫)."
  - Otherwise a nontrivial `a ∈ A` lying in `⟪w⟫` gives a boundary-incompressible
    `w`-admissible sphere with `k+1` boundary components and degree at least `k`.
    Their spectral gap theorem (Theorem `thmA: spectral gap theorem`) forces
    `k−1 ≥ deg(S) ≥ k`, a contradiction.
  - The proof works with right-orderable groups, which is equivalent: `g ↦ g^{-1}`
    turns a left order into a right order.

**Trust surface.** The input theorems (the spectral gap from relative stackings in
§5, and the existence of relative stackings in §6, Theorem `thm:StackingsRF`) were
not checked here. As far as seen, the paper is a preprint.
