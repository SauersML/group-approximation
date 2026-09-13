---
rg: 2
id: connected-rips-complexes-pass-to-direct-products-proof
kind: route
title: Project cliques of the strong product to both factors and apply Quillen's fiber lemma
target: connected-rips-complexes-pass-to-direct-products
requires: []
---

Write `A = Cay(G,T_G)` and `B = Cay(H,T_H)`.

**The Cayley graph is the strong product.** Distinct `(g,h), (g',h')` are
adjacent in `Cay(G × H, T)` iff `g^{-1}g' ∈ T_G ∪ {1}` and
`h^{-1}h' ∈ T_H ∪ {1}`, i.e. iff (`g = g'` or `g ~_A g'`) and (`h = h'` or
`h ~_B h'`). This is the strong product `A ⊠ B`. `T` is finite and symmetric.

**Quillen fiber lemma.** Let `P` be the face poset of `Flag(A ⊠ B)` (finite
nonempty cliques) and `Q = P(Flag A) × P(Flag B)`. For a clique `S` of `A ⊠ B`
the projections `π_A S` and `π_B S` are nonempty cliques, because two points of
`S` have equal or adjacent coordinates. So `f(S) = (π_A S, π_B S)` is a
monotone map `P → Q`. For `(σ, τ) ∈ Q`,
`f^{-1}(Q_{<= (σ,τ)}) = {S ≠ ∅ : π_A S ⊆ σ, π_B S ⊆ τ}` is the set of all
nonempty subsets of `σ × τ`. Each of these is a clique of `A ⊠ B` (coordinates
lie in cliques), so the fiber is the face poset of a simplex, which has a
maximum and is contractible. Quillen's fiber lemma (Quillen, *Homotopy
properties of the poset of nontrivial p-subgroups*, Prop. 1.6) shows that `f`
induces a homotopy equivalence of order complexes
`Δ(P) ≃ Δ(Q)`.

**Identify the order complexes.** `Δ(P)` is the barycentric subdivision of
`Flag(A ⊠ B)`. `Δ(P(K) × P(L))` is a triangulation of `|K| × |L|` for locally
finite simplicial complexes `K, L` (the order complex of a product of posets
is homeomorphic to the product of order complexes). Hence
`Flag(A ⊠ B) ≃ Flag(A) × Flag(B)`.

**Connectivity.** `π_k(X × Y) ≅ π_k(X) × π_k(Y)`, so the product of two
(n−1)-connected spaces is (n−1)-connected. If `R_{t}(G,S)` and `R_{t'}(H,S')`
are (n−1)-connected, apply the above with `T_G = B_S(t) \ {1}` and
`T_H = B_{S'}(t') \ {1}`, then use item 2 of
`group-rips-complexes-are-cayley-graph-flag-complexes` to read
`Flag(Cay(G × H, T))` as a Rips complex of `G × H`. ∎
