---
rg: 2
id: lot-complexes-with-at-most-six-vertices-are-aspherical
kind: claim
title: Every labelled oriented tree complex with at most six vertices is aspherical, by an exhaustive census certified with injectivity and the one-cycle criterion
distinct_from:
  contractible-2-complex-minus-a-cell-is-aspherical: that is the open finite one-cell case of Whitehead's conjecture, which contains every LOT complex; this settles only LOT complexes with at most six vertices.
  lot-complexes-with-vanishing-first-l2-betti-are-aspherical: that derives asphericity of a LOT complex from an L²-Betti hypothesis on its group; this needs no hypothesis but covers only trees with at most six vertices.
artifacts:
  - research/artifacts/hl-whitehead-lot-certify-2026-09-14.md
---

**ESTABLISHED** through `lot-at-most-six-vertices-census-proof`.

**Setup.** A labelled oriented tree (LOT) Γ is a finite tree with vertex set V, where each edge e
is oriented from i(e) to t(e) and carries a label λ(e) ∈ V. Its group has the presentation

  G(Γ) = ⟨ V | i(e) λ(e) = λ(e) t(e)  (e an edge of Γ) ⟩,

and K(Γ) is the presentation 2-complex.

**Claim.** If Γ has at most six vertices, then K(Γ) is aspherical.

**Context.**
- By item 1 of `lot-complexes-with-vanishing-first-l2-betti-are-aspherical`, K(Γ) is a one-cell
  complement in a contractible 2-complex. So a non-aspherical LOT complex would refute
  `contractible-2-complex-minus-a-cell-is-aspherical`.
- LOT complexes are the spines of ribbon disc complements (Rosebrock's 2007 survey).
- On seven vertices, 13 of the 279943 classes of reduced LOTs survive every implemented test
  (primary pipeline, artifact §3). Seven is not settled here.

**Novelty.** Not verified. A small-vertex census of LOTs may already be in print; Rosebrock's 2018
LMS Lecture Notes 446 chapter was not read.
