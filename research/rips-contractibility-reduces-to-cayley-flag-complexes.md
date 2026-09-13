---
rg: 2
id: rips-contractibility-reduces-to-cayley-flag-complexes
kind: claim
title: A group has a contractible Rips complex iff it acts simply transitively on the vertices of a contractible flag complex
distinct_from:
  contractible-rips-complex-gives-finite-classifying-space: that says what a contractible Rips complex gives (a finite K(G,1) for torsion-free G); this rewrites the property itself as a statement about Cayley flag complexes and vertex-transitive actions
---

Let `G` be a finitely generated group. For a finite symmetric generating set
`S ∌ 1` write `R_r(G,S)` for the closed Rips complex (vertex set `G`, simplices
the finite subsets of `d_S`-diameter `≤ r`). Then:

1. `R_r(G,S) = R_1(G, S_r)` as simplicial complexes, where
   `S_r = B_S(r) ∖ {1}`.
2. `R_1(G,S)` is the flag (clique) complex of the Cayley graph `Cay(G,S)`.
3. The following are equivalent:
   - (a) `R_r(G,S)` is contractible for some finite symmetric generating set `S`
     and some scale `r ≥ 1`;
   - (b) the flag complex of `Cay(G,S)` is contractible for some finite
     symmetric generating set `S`;
   - (c) `G` acts simplicially on a locally finite, contractible flag simplicial
     complex, simply transitively on its vertex set.

So "has a contractible Rips complex", the reading of Problems 4.6 and 4.7 in
`zaremsky-4-06-f-infinity-finite-cd-contractible-rips`, needs only scale 1, and
it depends only on which Cayley graphs `G` has. Scales `r ≥ 1` are integers
without loss, since `d_S` is integer-valued.

Proof: `rips-contractibility-reduces-to-cayley-flag-complexes-proof`.
