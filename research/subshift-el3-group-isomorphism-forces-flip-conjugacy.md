---
rg: 2
id: subshift-el3-group-isomorphism-forces-flip-conjugacy
kind: claim
title: Open - does G_X ≅ G_Y imply that the infinite minimal subshifts X and Y are flip conjugate?
distinct_from:
  subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence: that is the strong orbit equivalence conclusion, established through Theorem D; this asks for the stronger conclusion, flip conjugacy
  subshift-el3-isomorphisms-are-standard-over-f2: that gives the standard form inn(k)∘M_3(φ) of every isomorphism; this asks whether that form forces flip conjugacy
  subshift-elementary-group-diagonal-iso-gives-flip-conjugacy: that assumes the isomorphism carries the diagonal onto the diagonal; this asks it for every abstract isomorphism
  topological-full-groups-determine-flip-conjugacy: that is the theorem for topological full groups; this is the question for the elementary groups G_X of the note
  corner-matrix-ring-isos-force-flip-conjugacy: that is about ring isomorphisms assembled from diagonal-preserving corner maps; this is about abstract group isomorphisms
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that asks for strong orbit equivalence over every finite field modulo the centre; this asks for flip conjugacy over F_2
---

**OPEN.** Let `X, Y` be infinite minimal subshifts and `G_X = EL_3(LC(X,F_2) ⋊ Z)`. Flip conjugacy of `(X,T)` and
`(Y,T′)` gives `G_X ≅ G_Y`. Does the converse hold?

This is the first alternative of the rigidity question in the Questions section of `simple_kazhdan_sofic_group.tex`.
The second alternative, strong orbit equivalence, is established
(`subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence`, through Theorem D). For topological full groups the
converse holds (`topological-full-groups-determine-flip-conjugacy`).

## Attempts

- **Standard form plus Cartan uniqueness.** By `subshift-el3-isomorphisms-are-standard-over-f2`, every isomorphism is
  `inn(k)∘M_3(φ)|_{G_X}`, possibly after the graph automorphism, for a ring isomorphism `φ: R_X → R_Y`.
  - Suppose `φ(LC(X,F_2)) = θ(LC(Y,F_2))` for a ring automorphism `θ` of `R_Y`. Then `M_3(θ^{-1}∘φ)` is an isomorphism
    `G_X → G_Y` carrying the diagonal onto the diagonal, and `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`
    gives flip conjugacy.
  - Where it dies: that hypothesis would follow from Cartan uniqueness for `R_Y`,
    `subshift-crossed-product-algebraic-cartans-are-conjugate`, provided `φ(LC(X,F_2))` is an algebraic Cartan
    subalgebra in that node's sense. Cartan uniqueness is open, and by
    `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity` it is equivalent to rigidity of effective groupoid
    models.
- Bound: only main's graph and the reviews sk-verify-25a and sk-verify-25b were consulted; no literature search was
  made for this node (sk-rigidity-merge, 2026-09-14).
