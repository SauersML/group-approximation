---
rg: 2
id: contractible-rips-groups-closed-under-direct-products-proof
kind: route
title: The l-infinity word metric makes the product Rips complex a categorical product, and Quillen's fiber lemma compares it with the product space
target: contractible-rips-groups-closed-under-direct-products
requires: []
---

**1. Metric.** Words in `S ⊠ T` project to words in `S` and `T` that are no
longer, so `d_{S⊠T} ≥ max(d_S, d_T)`. Conversely, if
`g^{-1}g' = s_1 ⋯ s_m` and `h^{-1}h' = t_1 ⋯ t_n` with `m ≥ n`, pad the second
word with `t_{n+1} = ⋯ = t_m = 1`. Each `(s_i, t_i)` lies in `S ⊠ T` since
`s_i ≠ 1`, so `(g,h)^{-1}(g',h') = (s_1,t_1) ⋯ (s_m,t_m)` has length `m`.

**2. Simplices.** A finite `σ ⊆ G × H` has all pairwise `d_{S⊠T}`-distances
`≤ r` iff all pairwise `d_S`-distances in `π_G σ` and `d_T`-distances in
`π_H σ` are `≤ r`. Every pair in a projection is the projection of a pair in
`σ`. So `σ ∈ R_r(G×H)` iff `π_G σ ∈ R_r(G)` and `π_H σ ∈ R_r(H)`. That is the
categorical product `K ⊓ L` of `K = R_r(G,S)` and `L = R_r(H,T)`.

**3. Homotopy type.** Let `F(·)` be the face poset. The map
`f : F(K ⊓ L) → F(K) × F(L)`, `σ ↦ (π_G σ, π_H σ)`, is order-preserving. Its
fiber over `(a,b)` is `{σ : π_G σ ⊆ a, π_H σ ⊆ b}`, which is the set of all
nonempty subsets of the finite set `a × b`: every such subset has projections
that are faces of `a` and `b`. This poset has a maximum `a × b`, so its order
complex is a cone and is contractible. By Quillen's fiber lemma (D. Quillen,
*Homotopy properties of the poset of nontrivial p-subgroups of a group*, Adv.
Math. 28 (1978); the proposition number was not re-read), `f` induces a homotopy
equivalence of order complexes. The order complex of a face poset is the
barycentric subdivision, so `|Δ F(K ⊓ L)| ≅ |K ⊓ L|`. The nerve of a product
poset is the product of the nerves, and realization commutes with finite
products of simplicial sets (Milnor 1957) in compactly generated spaces. For
these countable, locally finite complexes that is the usual product. So
`|Δ(F(K) × F(L))| ≅ |K| × |L|`, and `|K ⊓ L| ≃ |K| × |L|`.

**4. Consequences.** A product of contractible spaces is contractible. For
type `ℝ`, take `r_0` as the larger of the two thresholds. For the weak reading,
item 1 of `rips-complex-of-a-group-is-a-flag-cayley-complex` rewrites
`R_r(G,S)` and `R_{r'}(H,T)` as scale-1 Rips complexes
(`R_r(G,S) = R_1(G, B_S(r) ∖ {1})`), and then apply part 2 at `r = 1`.
