---
rg: 2
id: rips-complex-of-a-group-is-a-flag-cayley-complex
kind: claim
title: A group has a contractible Rips complex iff it acts simply transitively on the vertices of a contractible flag complex
---

Let `G` be a finitely generated group. For a finite generating set `S` and a scale
`r ≥ 1`, write `B = {g ≠ 1 : |g|_S ≤ r}`. Then

1. `VR_r(G, d_S)` equals the flag (clique) complex of the Cayley graph `Cay(G, B)`.

The following are equivalent:

- (a) `VR_r(G, d_S)` is contractible for some finite generating set `S` and some
  scale `r`;
- (b) the flag complex of `Cay(G, T)` is contractible for some finite symmetric
  generating set `T` with `1 ∉ T`;
- (c) `G` acts freely and cocompactly on a contractible locally finite flag
  simplicial complex `X`, transitively on the vertices of `X`.

2. If these hold, every simplex stabilizer is finite, so `G` is of type `F_*`
   (a geometric action on a contractible complex); if moreover `G` is
   torsion-free, `X/G` is a finite `K(G,1)` and `G` is of type F. The complex
   `X` in (c) has dimension `≤ |T|`.

Proof: route `rips-complex-of-a-group-is-a-flag-cayley-complex-proof`.
