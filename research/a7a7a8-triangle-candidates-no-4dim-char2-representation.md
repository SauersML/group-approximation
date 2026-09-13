---
rg: 2
id: a7a7a8-triangle-candidates-no-4dim-char2-representation
kind: claim
title: The four explicit (A_7, A_7, A_8) hyperbolic triangle candidates have no nontrivial 4-dimensional representation in characteristic 2
---

Let `G_1, …, G_4` be the four hyperbolic triangles of groups with vertex groups
`(A_7, A_7, A_8)`, edge groups `Z/7`, trivial face group and half-girth type `(3,3,4)`.
They are recorded in `research/artifacts/simple-vertex-triangle-quotient-search-2026-09-12.md`
§2, with data in `experiments/hyperbolic-triangle-search/cands.g`.

For every field `K` of characteristic 2 and each `i`, every homomorphism
`G_i -> GL_4(K)` is trivial. So no `G_i` has a nontrivial finite quotient with a faithful
4-dimensional representation over a field of characteristic 2.
- For `G_2` and `G_4` this follows from an eigenvalue sign obstruction:
  `σ(G) = τ(x_A)τ(y_A)τ(x_B)τ(y_B)τ(x_C)τ(y_C)χ(e_1e_2e_3) = -1`.
- For `G_1` and `G_3` it follows from a Gröbner basis certificate: the trace ideal is `(1)`.

The result is computer-assisted (Sage 10.7 / Singular) and unreviewed.
