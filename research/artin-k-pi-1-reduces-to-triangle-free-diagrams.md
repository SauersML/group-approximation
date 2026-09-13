---
rg: 2
id: artin-k-pi-1-reduces-to-triangle-free-diagrams
kind: claim
title: "Huang–Przytycki: the K(π,1) conjecture for all Artin groups follows from a girth condition and contractible Artin complexes for triangle-free diagrams"
distinct_from:
  artin-k-pi-1-reduces-to-free-of-infinity-parabolics: that is the Godelle–Paris reduction of one group to its free-of-infinity parabolic subgroups; this reduces the whole conjecture to two properties of triangle-free Coxeter diagrams.
  artin-k-pi-1-from-contractible-artin-complex: that is the one-step criterion for a single diagram; this is the global induction over diagrams with and without triangles.
---

Let `Λ` be a Coxeter diagram (edges `st` for `m_st ≥ 3`, including `m_st = ∞`) with Artin
complex `Δ_Λ` (see `artin-k-pi-1-from-contractible-artin-complex`). For an induced subdiagram
`Λ'`, the *relative Artin complex* `Δ_{Λ,Λ'}` is the induced subcomplex of `Δ_Λ` spanned by
vertices of type `ŝ` with `s ∈ Λ'`. The diagram `Λ` satisfies the *girth condition* when for
each edge `st` of `Λ` the graph `Δ_{Λ,st}` has girth at least 6. A *triangle* is an embedded
3-cycle of `Λ`.

**Reduction.** Suppose every non-spherical `Λ` without triangles satisfies the girth condition
and has contractible `Δ_Λ`. Then every Artin group satisfies the K(π,1) conjecture.

More generally, for a class `𝒞` of diagrams closed under induced subdiagrams and a subclass
`𝒞_1 ⊆ 𝒞` containing every triangle-free member of `𝒞`: if each diagram in `𝒞_1` satisfies
the girth condition and each non-spherical one has contractible Artin complex, then each
diagram in `𝒞` satisfies the K(π,1) conjecture.

Literature import through `artin-k-pi-1-reduces-to-triangle-free-diagrams-citation`, from a
preprint (September 2025) that this graph has not reviewed.
