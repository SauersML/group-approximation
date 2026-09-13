---
rg: 2
id: triangle-free-coxeter-diagrams-girth-and-contractible-complex
kind: claim
title: Every triangle-free Coxeter diagram satisfies the girth condition, and its Artin complex is contractible when it is non-spherical
distinct_from:
  free-of-infinity-artin-groups-satisfy-k-pi-1: that is the K(π,1) conjecture for diagrams with finite labels; this is a pair of combinatorial-topological properties of Artin complexes for triangle-free diagrams, which implies the conjecture through the Huang–Przytycki reduction.
---

For every Coxeter diagram `Λ` (labels `3, …, ∞` on edges) with no embedded 3-cycle:

1. for each edge `st` of `Λ`, the relative Artin complex `Δ_{Λ,st}` has girth at least 6;
2. if `W_Λ` is infinite, the Artin complex `Δ_Λ` is contractible.

With `artin-k-pi-1-reduces-to-triangle-free-diagrams` this gives the K(π,1) conjecture for
every Artin group (route `artin-k-pi-1-via-triangle-free-diagrams`).

## Attempts

- Known (arXiv:2509.06914, Theorem `thm:4` and Theorem `thm:general`): both properties when
  `Λ^c` has no embedded 4-cycle; when `Λ` is locally reducible; when `Λ` satisfies the tree
  hypothesis of arXiv:2305.16847 Theorem 1.1; for `K_{k,l}` with `k, l ≥ 2`.
- Theorem `thm:4` leaves only diagrams whose complement `Λ^c` has an embedded 4-cycle. On
  at most 4 vertices such a triangle-free `Λ` lies inside a perfect matching, so `Δ_Λ` is a
  join of dihedral Artin complexes and both properties hold. A connected one on 5 vertices
  is the path `P_5`, the tree with arms of lengths 1, 1, 2 at a vertex of degree 3, or the
  star `K_{1,4}` (lane z1-05-artin-kpi1). Stars are handled in arXiv:2405.12068; some labelings
  of the first two shapes are covered (spherical, affine, locally reducible, cut by a label
  at least 6), and the compact hyperbolic 4-simplex diagrams `[5,3,3,3]`, `[4,3,3,5]`,
  `[5,3,3,5]`, `[5,3,3^{1,1}]` are not.
