---
rg: 2
id: artin-k-pi-1-reduces-to-triangle-free-diagrams-citation
kind: route
title: Import the Huang–Przytycki triangle reduction for the K(π,1) conjecture
target: artin-k-pi-1-reduces-to-triangle-free-diagrams
requires: []
---

Citation import, not a reproof. Read on 2026-09-13 from the arXiv LaTeX source of
J. Huang and P. Przytycki, *353-combinatorial curvature and the 3-dimensional K(π,1)
conjecture*, arXiv:2509.06914 (submitted 8 September 2025). Parts read: the introduction,
Section 2 (Artin complex), the section on relative Artin complexes, the statements of the
section on 3-dimensional Artin groups, Proposition `prop:triangle`, Corollary
`cor:reduction` and Theorem `thm:general`. Not read: the proofs of Parts I and II.

Verbatim:

- Definition (section on 3-dimensional Artin groups): "We say that a Coxeter diagram Λ
  satisfies the girth condition if for each edge st of Λ, the graph Δ_{Λ, st} has girth ≥ 6."
- Proposition `prop:triangle`: "Let 𝒞 be a class of Coxeter diagrams closed under taking
  induced subdiagrams. Suppose that we have 𝒞_1 ⊂ 𝒞 such that each diagram in 𝒞 − 𝒞_1
  contains a triangle. Then (1) if each diagram in 𝒞_1 satisfies the girth condition, then
  each diagram in 𝒞 satisfies the girth condition, and (2) if in addition for each
  nonspherical Λ_1 ∈ 𝒞_1 the Artin complex Δ_{Λ_1} is contractible, then for each
  nonspherical Λ ∈ 𝒞 the Artin complex Δ_Λ is contractible. In particular, each diagram in
  𝒞 satisfies the K(π,1) conjecture."
- Corollary `cor:reduction`: "Suppose that all non-spherical Λ without triangles satisfy the
  girth condition and have contractible Δ_Λ. Then all Artin groups satisfy the K(π,1)
  conjecture."
- Preliminaries: "A Coxeter diagram Λ is a finite simplicial graph with vertex set
  S={s_i}_i and labels m_ij=3,4,…,∞ for each edge s_is_j. If s_is_j is not an edge, we
  define m_ij=2."

Trust: an unrefereed preprint as far as this graph knows. Its reduction rests on Theorem
`thm:Kpi1` (see `artin-k-pi-1-from-contractible-artin-complex`) and on a systolic/CAT(0)
argument for triangles in the proof of Proposition `prop:triangle`.
