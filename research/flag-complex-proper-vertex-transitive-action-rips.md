---
rg: 2
id: flag-complex-proper-vertex-transitive-action-rips
kind: claim
title: A proper vertex-transitive action on a contractible flag complex gives a contractible Rips complex, even with finite vertex stabilizers
distinct_from:
  rips-complex-of-a-group-is-a-flag-cayley-complex: that is the same simply transitive equivalence stated directly; this is the extension to finite vertex stabilizers by collapsing twin vertices
---

**ESTABLISHED** (route `flag-complex-proper-vertex-transitive-action-rips-proof`).

Let `X` be a locally finite, contractible flag simplicial complex, and let a
group `G` act on `X` by simplicial automorphisms, transitively on the vertex set
`X^0`, with finite vertex stabilizers. Fix a vertex `v` and put

`S = {g ∈ G ∖ {1} : g v = v or g v is adjacent to v}`.

Then `S` is a finite symmetric generating set of `G`, and the Rips complex
`P_1(G,S)`, the clique complex of `Cay(G,S)`, is homotopy equivalent to `X`. In
particular `P_1(G,S)` is contractible.

When the stabilizers are trivial this is (c) ⇒ (b) of
`rips-complex-of-a-group-is-a-flag-cayley-complex`. The new case is a
nontrivial stabilizer: the vertices of `P_1(G,S)` over one vertex of `X` form a
coset of the stabilizer, they are pairwise adjacent twins, and collapsing them
recovers `X`.

Uses in the graph: groups with torsion acting on lattice complexes
(`linf-preserving-proper-actions-give-contractible-rips`), and groups with
torsion acting geometrically on asymptotically CAT(0) spaces
(`asymptotically-cat0-groups-have-contractible-rips`).
