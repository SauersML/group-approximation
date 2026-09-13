---
rg: 2
id: rips-contractibility-reduces-to-cayley-flag-complexes-proof
kind: route
title: Rescale the generating set to scale one and read off the Cayley graph from a vertex-transitive action
target: rips-contractibility-reduces-to-cayley-flag-complexes
requires: []
---

**1.** Put `S_r = B_S(r) ∖ {1}`, a finite symmetric generating set. For
`g, h ∈ G` with `n = d_S(g,h)`, `d_{S_r}(g,h) = ⌈n/r⌉`: `g^{-1}h` is a product of
`⌈n/r⌉` elements of `S`-length `≤ r`, and a product of `m` elements of `S_r` has
`S`-length `≤ mr`. So `d_{S_r}(g,h) ≤ 1` iff `d_S(g,h) ≤ r`. A finite set is a
simplex of `R_1(G,S_r)` iff all its pairwise `S_r`-distances are `≤ 1`, iff all
pairwise `S`-distances are `≤ r`, iff it is a simplex of `R_r(G,S)`.

**2.** A finite subset of `G` has diameter `≤ 1` iff its elements are pairwise
equal or adjacent in `Cay(G,S)`, i.e. iff it is a clique.

**3.** (a) ⇒ (b) by part 1, with generating set `S_r`. (b) ⇒ (c): `G` acts on
`R_1(G,S)` by left multiplication, simplicially and simply transitively on
vertices; `R_1(G,S)` is flag by part 2 and locally finite because `S` is finite.
(c) ⇒ (a): let `X` be such a complex and `v_0` a vertex. The orbit map
`g ↦ g v_0` is a bijection `G → X^{(0)}`. Put
`S = {s ∈ G : s v_0 and v_0 span an edge}`. It is finite (local finiteness),
symmetric (apply `s^{-1}`) and does not contain `1`. Since the action preserves
edges, `g v_0` and `h v_0` span an edge iff `v_0` and `g^{-1}h v_0` do, iff
`g^{-1}h ∈ S`. So the 1-skeleton of `X` is `Cay(G,S)` under the orbit
bijection. `X` is connected, so `S` generates `G`. `X` is flag, so it is the
flag complex of its 1-skeleton, which is `R_1(G,S)` by part 2. So `R_1(G,S)` is
contractible.
