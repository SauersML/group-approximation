---
rg: 2
id: bestvina-brady-groups-have-connected-rips-complexes-proof
kind: route
title: The Bestvina-Brady level set is the vertex-transitive cube level set, and Morse theory makes it highly connected
target: bestvina-brady-groups-have-connected-rips-complexes
requires:
  - cube-level-set-clique-complexes-model-the-level-set
artifacts:
  - research/artifacts/zp-cube-level-set-rips-2026-09-13.md
---

Source: M. Bestvina, N. Brady, *Morse theory and finiteness properties of
groups*, Invent. Math. 129 (1997), 445–470 (BB97), read 2026-09-13.

**1. The cube complex and the Morse function.** BB97 Theorem 5.12 gives a
nonpositively curved PE cubical complex `Q_L` with one vertex and
`π_1 = A_Γ` (the Salvetti complex). By Theorem 5.12(3), the lift of
`l: Q_L → S^1` is a `φ`-equivariant Morse function `f: X → R` on the universal
cover `X`, and by Theorem 5.12(4) all ascending and descending links are
isomorphic to `L`. `X` is a simply connected nonpositively curved cube
complex, hence a CAT(0) cube complex, and `A_Γ` acts freely and transitively on
its vertices. The proof of Theorem 5.12 shows that on each cube `f` is an
integer translate of `x ↦ Σ x_i`. So `f` is integer-valued on vertices and
changes by exactly `1` along edges. Translate `f` so that `f(v_0) = 0` at a
base vertex `v_0`.

**2. Theorem A applies.** Since `f(g x) = φ(g) + f(x)`, `H_L` preserves `f`,
and `V_0 = f^{-1}(0) ∩ X^(0) = H_L · v_0` with free transitive action. The
cubes through `v_0 = 1` are the standard cubes with vertex sets
`{∏_{v∈β} v^{-1} · ∏_{v∈τ} v : τ ⊆ σ}` for simplices `σ` of `L` and `β ⊆ σ`.
The vertex for `τ` equals `∏_{v∈τ\β} v · ∏_{w∈β\τ} w^{-1}` and has height
`|τ\β| − |β\τ|`. So the height-0 vertices other than `1` are the products over
disjoint `α = τ\β` and `β' = β\τ` with `|α| = |β'| >= 1`, and every such pair
occurs (take `β = β'`, `τ = α`). These are exactly the elements of `T`. By `cube-level-set-clique-complexes-model-the-level-set`
(item 3), `Flag(Cay(H_L, T)) ≃ L_0 := f^{-1}(0)`.

**3. Connectivity of the level set.** BB97 Corollary 2.6 applies to the
nonempty connected `J = {0} ⊆ J' = R`, with `X_{J'} = X` contractible:

- (2): if every ascending and descending link is simply connected, then
  `X_J ↪ X_{J'}` is an isomorphism on `π_1`;
- (1): if every link is homologically `m`-connected, then it is an isomorphism
  on `H̃_i` for `i <= m`.

The links are copies of `L`. If `L` is (n−1)-connected with `n >= 2`, this
gives `π_1(L_0) = 1` and `H̃_i(L_0) = 0` for `i <= n−1`, so `L_0` is
(n−1)-connected by Hurewicz. If `n = 1`, (1) with `m = 0` gives `H̃_0(L_0) = 0`,
so `L_0` is connected.

**4. Conclusion.** `Flag(Cay(H_L,T))` is (n−1)-connected, in particular
connected, so `T` generates `H_L` and `Flag(Cay(H_L,T)) = R_1(H_L,T)`
(`group-rips-complexes-are-cayley-graph-flag-complexes`).

**5. Type `F_n`.** BB97 Main Theorem (over `R = Z`): (1) `H_L ∈ FP_{m+1}` iff
`L` is homologically `m`-connected; (3) `H_L` is finitely presented iff `L` is
simply connected. For `n >= 2`, type `F_n` means finitely presented and
`FP_n`, i.e. `L` simply connected and homologically (n−1)-connected, i.e. `L`
(n−1)-connected by Hurewicz. For the octahedral `n`-sphere `L = S^n`,
`H̃_n(L) ≠ 0`, so `H_L` is not `FP_{n+1}`. ∎
