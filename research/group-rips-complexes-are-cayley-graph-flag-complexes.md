---
rg: 2
id: group-rips-complexes-are-cayley-graph-flag-complexes
kind: claim
title: Rips complexes of a group are exactly the clique complexes of its finite Cayley graphs
distinct_from:
  rips-complex-of-a-group-is-a-flag-cayley-complex: that gives the same identification of Rips complexes with Cayley clique complexes and the equivalence for contractible complexes, plus the type F_* and type F consequences; this gives the equivalence for (n-1)-connected complexes, the form Zaremsky Problem 4.4 needs
---

Let `G` be a finitely generated group. For a finite generating set `S` and
`t >= 0`, write `R_t(G,S)` for the Rips complex of `(G, d_S)` (simplices: finite
nonempty sets of diameter `<= t`), `B_S(t)` for the ball of radius `t` about
`1`, and `Flag(Γ)` for the clique complex of a graph `Γ`. For a finite
symmetric `T ⊆ G \ {1}`, `Cay(G,T)` has vertex set `G` and edges `{g, gs}`,
`s ∈ T`.

1. `R_t(G,S) = Flag(Cay(G, B_S(t) \ {1}))`, and `Flag(Cay(G,T)) = R_1(G,T)`
   whenever `T` generates `G`.
2. For each `n >= 1` the following are equivalent:
   - (a) `R_t(G,S)` is (n−1)-connected for some finite generating set `S` and
     some `t >= 0`;
   - (b) `Flag(Cay(G,T))` is (n−1)-connected for some finite symmetric
     `T ⊆ G \ {1}`;
   - (c) `G` acts simplicially and cocompactly on an (n−1)-connected flag
     simplicial complex, freely and transitively on its vertex set.

So Zaremsky Problem 4.4 for a given `n` asks whether every group of type `F_n`
has a Cayley graph, for some finite generating set, whose clique complex is
(n−1)-connected.

Credit: item 1 is observed in Zaremsky, arXiv:1812.10976, Remark 6.6, for
contractibility ("VR_1(G) is the flagification of the Cayley graph"). Items
2(b)⇔(c) are the elementary translation used here.

Proof: `group-rips-complexes-are-cayley-graph-flag-complexes-proof`.
