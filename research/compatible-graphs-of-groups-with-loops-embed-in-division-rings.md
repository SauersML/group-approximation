---
rg: 2
id: compatible-graphs-of-groups-with-loops-embed-in-division-rings
kind: claim
title: A D-compatible graph of groups, loops and HNN edges included, has group ring inside a division ring, with vertex division rings sitting inside it and vertex transversals independent
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports the Fisher--Sanchez-Peralta corollary for locally indicable vertex groups, whose source proof treats only separating edges and says the non-separating (HNN) case is "proved similarly"; this proves the HNN case independently, through the infinite cyclic cover and the extension of the shift to the universal field of fractions, and records the inductive independence property that later permanence arguments need.
  higman-group-algebras-embed-in-division-rings: that is one application over a tree with one edge; this is the general graph statement with cycles, which is what lattices acting on a tree with loops in the quotient require.
---

**ESTABLISHED** by [[loop-graphs-of-division-rings-proof]]. Not yet independently re-derived.

Let `k` be a division ring and let `(G_v, G_e)` be a graph of torsion-free groups over a connected graph `Gamma`,
with fundamental group `G`. Following Fisher--Sanchez-Peralta (arXiv:2303.08165, Section 3), the graph is
**D-compatible** if:

1. for every vertex `v` there is an embedding `k[G_v] -> D_v` into a division ring;
2. for every edge `e`, with `D_e := Div(k[G_e], D_(t(e)))`, every right transversal of `G_e` in `G_(t(e))` is left
   linearly independent over `D_e`;
3. `D_e ≅ D_(ebar)` as `k[G_e]`-rings.

**Theorem.** If `(G_v, G_e)` is D-compatible, then `k[G]` embeds in a division ring `Q`. If `Gamma` is finite,
`Q` can be chosen so that the following property **(P)** also holds for every vertex `v`: the embedding
`k[G_v] -> Q` extends to an embedding `D_v -> Q`, and every right transversal of `G_v` in `G` is left linearly
independent over `D_v` inside `Q`.

For a separating edge the argument is that of the source (Proposition 3.12 and Theorem 3.13 there, via Cohn
coproducts of semifirs and Dicks' normal form). The source omits the non-separating case. Here it is reduced to the
separating case on a line of groups:
- the kernel `N` of `A *_C -> Z` is the fundamental group of a D-compatible bi-infinite line;
- the shift automorphism of the line's semifir extends to its universal field of fractions `U`;
- then `k[A *_C] = k[N][t^(±1); sigma]` sits inside the Ore domain `U[t^(±1); sigma]`.

Infinite graphs follow by an ultraproduct over finite subgraphs.
