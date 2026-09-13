---
rg: 2
id: torsion-free-contractible-rips-complex-gives-type-f-proof
kind: route
title: The free cocompact action on a contractible Rips complex gives a finite classifying space
target: torsion-free-contractible-rips-complex-gives-type-f
requires: []
---

Write `P = P_r(G,S)` and `|P|` for its geometric realization (weak topology).

1. **Simplicial action.** Left multiplication preserves the word metric:
   `d_S(gx, gy) = |x^-1 g^-1 g y|_S = d_S(x,y)`. So each `g` maps simplices
   (finite sets of diameter `<= r`) to simplices, and `G` acts on `P` by
   simplicial automorphisms.
2. **No simplex is stabilized.** If `g σ = σ` for a simplex `σ`, then `g`
   permutes the finite set `σ`, so `g^m` fixes a vertex `x` for `m = |σ|!`.
   Then `g^m x = x` gives `g^m = 1`, and `g = 1` because `G` is torsion-free.
3. **Covering space action.** Let `sd P` be the barycentric subdivision and
   `b_σ` the barycenter of `σ`. A point `p` in the open simplex of `σ` lies in
   the open star `U = st_{sd P}(b_σ)`. If `U ∩ gU` is nonempty, then `b_σ` and
   `g b_σ = b_{gσ}` span an edge or coincide in `sd P`, so `σ` and `gσ` are
   comparable under inclusion. They have the same number of vertices, so
   `gσ = σ` and `g = 1` by step 2. Hence every point has a neighbourhood
   disjoint from all its nontrivial translates, and `|P| -> |P|/G` is a
   covering map with deck group `G` (Hatcher, *Algebraic Topology*,
   Proposition 1.40).
4. **Classifying space.** `|P|` is contractible, hence simply connected with
   all higher homotopy groups trivial. So it is the universal cover of `|P|/G`,
   `π_1(|P|/G) = G`, and `π_k(|P|/G) = 0` for `k >= 2`: `|P|/G` is a `K(G,1)`.
5. **Finiteness.** By step 2 the action is free and permutes open simplices
   freely, so `|P|/G` is a CW complex with one cell for each `G`-orbit of
   simplices. Every simplex `σ` has a translate `x^-1 σ` (for any `x ∈ σ`)
   that contains `1`, and a simplex containing `1` is a subset of `B_S(r)`.
   There are finitely many such subsets, so there are finitely many cells, of
   dimension at most `|B_S(r)| - 1`.

So `G` has a finite `K(G,1)` of dimension at most `|B_S(r)| - 1`. That is,
`G` is of type F and `cd G <= |B_S(r)| - 1`.
