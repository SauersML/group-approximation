---
rg: 2
id: boundary-crossed-product-embeds-unitally-in-binary-leavitt-proof
kind: route
title: Leavitt path algebra of a finite graph, then Brownlowe–Sørensen Theorem 4.1 with finitely many vertices
target: boundary-crossed-product-embeds-unitally-in-binary-leavitt
requires:
  - boundary-crossed-product-is-a-leavitt-path-algebra
  - countable-graph-leavitt-path-algebras-embed-in-binary-leavitt
---

By `boundary-crossed-product-is-a-leavitt-path-algebra`, `LC(∂F_d, k) ⋊ F_d ≅ L_k(E_d)`, where `E_d` has `2d`
vertices and finitely many edges.

`countable-graph-leavitt-path-algebras-embed-in-binary-leavitt` (Brownlowe–Sørensen, arXiv:1503.08705v3,
Theorem 4.1: "if E0 is ﬁnite, then this embedding can be chosen to be unital") gives a unital embedding
`L_k(E_d) -> L_k(1,2)`.

A unital injective ring homomorphism `iota : S -> T` maps elementary matrices to elementary matrices, so it
restricts to an injective homomorphism `EL_N(S) -> EL_N(T)`.
