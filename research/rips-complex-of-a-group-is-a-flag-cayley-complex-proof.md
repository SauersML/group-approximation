---
rg: 2
id: rips-complex-of-a-group-is-a-flag-cayley-complex-proof
kind: route
title: Direct proof that Rips complexes of groups are flag complexes of Cayley graphs
target: rips-complex-of-a-group-is-a-flag-cayley-complex
requires: []
---

Conventions: `d_S(g, h) = |g^{-1}h|_S`; `Cay(G, T)` has vertex set `G` and edges
`{g, gt}` for `t ∈ T`; a flag complex has as simplices the finite vertex sets that
are pairwise adjacent.

**Item 1.** A finite set `σ ⊆ G` is a simplex of `VR_r(G, d_S)` iff
`d_S(g, h) ≤ r` for all `g, h ∈ σ`, iff `g^{-1}h ∈ B` for all distinct
`g, h ∈ σ`, iff `σ` is a clique of `Cay(G, B)`. So the two complexes have the same
simplices.

**(a) ⇒ (b).** If `r < 1`, `VR_r(G, d_S)` is the discrete set `G`, contractible
only for `G = 1`, where `T = ∅` works. If `r ≥ 1`, take `T = B`: it is finite,
symmetric, avoids `1`, contains `S \ {1}` and so generates, and item 1 identifies
the complexes.

**(b) ⇒ (a).** `d_T(g, h) ≤ 1` iff `h = g` or `g^{-1}h ∈ T`, so the flag complex
of `Cay(G, T)` is `VR_1(G, d_T)`.

**(b) ⇒ (c).** Left multiplication acts on `Cay(G, T)` by graph automorphisms,
freely and transitively on vertices, hence simplicially on the flag complex `X`.
`X` is locally finite since the vertex `1` lies in finitely many simplices (all are
subsets of `{1} ∪ T`), and cocompact since every simplex has a translate containing
`1`.

**(c) ⇒ (b).** Fix a vertex `v`. The orbit map `g ↦ gv` is a bijection from `G` to
the vertex set. Put `T = {g : gv` adjacent to `v}`, finite by local finiteness,
symmetric, and `1 ∉ T`. Then `gv, hv` are adjacent iff `v, g^{-1}hv` are adjacent
iff `g^{-1}h ∈ T`, so the 1-skeleton of `X` is `Cay(G, T)` under the orbit map.
`X` is connected, being contractible, so `T` generates `G`. `X` is flag, so it
equals the flag complex of its 1-skeleton.

**Item 2.** An element fixing a simplex permutes its finitely many vertices and
acts freely on vertices, so the stabilizer embeds in the symmetric group on the
vertices and is finite. With finitely many orbits of cells this is a geometric
action on a contractible CW complex. If `G` is torsion-free the stabilizers are
trivial, the action is free, and the finite complex `X/G` is aspherical with
fundamental group `G`. A simplex containing `1` is a subset of `{1} ∪ T`, so
`dim X ≤ |T|`.
