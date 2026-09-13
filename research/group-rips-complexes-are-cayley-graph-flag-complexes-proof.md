---
rg: 2
id: group-rips-complexes-are-cayley-graph-flag-complexes-proof
kind: route
title: Diameter is a pairwise condition, and vertex-transitive flag complexes are Cayley clique complexes
target: group-rips-complexes-are-cayley-graph-flag-complexes
requires: []
---

Conventions: `d_S(g,h) = |g^{-1}h|_S`; `G` acts on the left.

**Item 1.** A finite set has diameter `<= t` iff each pair of its points is at
distance `<= t`, so `R_t(G,S)` is the flag complex of its 1-skeleton. Distinct
`g, h` are adjacent in `R_t(G,S)` iff `0 < |g^{-1}h|_S <= t`, i.e. iff
`g^{-1}h ∈ T_t := B_S(t) \ {1}`. That graph is `Cay(G, T_t)`; `T_t` is finite
and symmetric. For finite symmetric `T ⊆ G \ {1}` generating `G`,
`B_T(1) \ {1} = T`, so `R_1(G,T) = Flag(Cay(G,T))`.

**(a) ⇒ (b).** `R_t(G,S) = Flag(Cay(G,T_t))` by item 1.

**(b) ⇒ (a).** Since `n >= 1`, `Flag(Cay(G,T))` is connected, so `Cay(G,T)` is
connected and `T` generates `G` (if `G = {1}`, then `T = ∅` and `R_0(G,∅)` is a
point). By item 1, `Flag(Cay(G,T)) = R_1(G,T)`.

**(b) ⇒ (c).** Left multiplication preserves adjacency in `Cay(G,T)`, so `G`
acts simplicially on `Y = Flag(Cay(G,T))`, freely and transitively on
vertices. Every simplex `σ` has a vertex `g`, and `g^{-1}σ` is a simplex
containing `1`, all of whose vertices lie in the finite set `{1} ∪ T`. So there
are finitely many orbits of simplices.

**(c) ⇒ (b).** Let `Y` be such a complex, `v_0` a vertex, and let
`σ_1, …, σ_r` represent the simplex orbits. A simplex containing `v_0` has the
form `gσ_i` with `g w = v_0` for some vertex `w` of `σ_i`, and `w` determines
`g` because the action on vertices is free. So `v_0` lies in at most
`Σ_i |σ_i|` simplices, and `Y` is locally finite. Put
`T = {g ∈ G : g v_0` adjacent to `v_0}`. It is finite, symmetric
(`g v_0 ~ v_0` gives `v_0 ~ g^{-1} v_0`) and misses `1`. The bijection
`G → Y^(0)`, `g ↦ g v_0`, satisfies `g v_0 ~ h v_0 ⇔ v_0 ~ g^{-1}h v_0 ⇔
g^{-1}h ∈ T`, so it is an isomorphism `Cay(G,T) → Y^(1)`. As `Y` is flag,
`Y ≅ Flag(Y^(1)) ≅ Flag(Cay(G,T))`, which is therefore (n−1)-connected. ∎
