---
rg: 2
id: primitive-two-graph-fp-simple-embedding-proof
kind: route
title: Rescale until every vertex has two loops of each colour, pass through the degree skew product, multiply by the full 2-shift to kill homology, then apply Li and Matui
target: primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple
requires:
  - li-finite-k-graph-full-groups-are-f-infinity
  - li-ah-exact-sequence-for-minimal-comparison-groupoids
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
  - finite-k-graph-boundary-groupoid-standard-facts
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

Notation as in the target. Paths of degree `(k_1, k_2)` from `v` to `u` number
`(M_1^{k_1} M_2^{k_2})(u, v)` by unique factorization. `X = Λ^∞`, with degree cocycle
`c(x, m, y) = m` on `G_Λ` (standard facts, item 1).

**Step 0: choose n.** Primitivity gives `K` with `M_1^k > 0` and `M_2^k > 0` entrywise for
`k >= K`, so there are paths of every degree `>= (K, K)` between any two vertices.
`ρ(M_j) > 1`: an irreducible nonnegative integer matrix with spectral radius 1 is a
permutation matrix, a primitive one is `(1)`, and `M_j = (1)` makes every infinite path
periodic (the colour-`j` loop commutes past the other colour by a permutation of finite
order `r`, so `σ^{r ε_j} x = x`), contradicting aperiodicity. So `M_j^k(a, a) -> ∞`.
Fix `n >= K` with `M_j^n(a, a) >= 2` for all `a` and `j`.

**Step 1: rescaling.** `Λ^(n) = {λ : d(λ) ∈ nN²}` with degree `d/n` is a finite 2-graph
whose colour-`j` loops at `a` number `M_j^n(a, a) >= 2`. Its infinite path space is `X`.
`G_{Λ^(n)} ≅ c^{-1}(nZ²)`, an open subgroupoid of `G_Λ`. Indeed, if `σ^p x = σ^q y` and
`p - q ∈ nZ²`, choose `r` with `p + r ∈ nN²`; then `q + r ∈ nN²` and
`σ^{p+r} x = σ^{q+r} y`. Aperiodic points of `Λ` stay aperiodic for `Λ^(n)`.

**Step 2: skew product.** `T = (Z/n)²`, `c̄ = c mod n`, `H = G_Λ ×_c̄ T` with unit space
`X × T`, `s(g, b) = (s(g), b)` and `r(g, b) = (r(g), b + c̄(g))`. Then
`H|_{X × {0}} ≅ c^{-1}(nZ²) ≅ G_{Λ^(n)}`. For a global compact open bisection `B_f` of
`G_Λ`, `B̃_f = B_f × T` is a global compact open bisection of `H`. The map `f ↦ f̃` is a
homomorphism, since `c̄` is additive, and injective, since `f̃` acts as `f` on the first
coordinate. So `[[G_Λ]] ↪ [[H]]`.

**Step 3: compression into X × {0}.** Choose `R` with `#Λ^R > |A| n²` and distinct
`ρ_{v,a} ∈ Λ^R` for `(v, a) ∈ A × T`, with at least one path of degree `R` left over.
Choose `σ_{v,a} ∈ s(ρ_{v,a}) Λ v` with `d(σ_{v,a}) >= (K, K)` and
`d(σ_{v,a}) ≡ -a - R mod n` (Step 0). Put `λ_{v,a} = ρ_{v,a} σ_{v,a}`. The bisections
`ψ_{v,a} = {((λ_{v,a} z, d(λ_{v,a}), z), a) : z ∈ Z(v)}` map `Z(v) × {a}` onto
`Z(λ_{v,a}) × {0}`, because `a + d(λ_{v,a}) ≡ 0`. Their ranges lie in the pairwise
disjoint cylinders `Z(ρ_{v,a})` and miss the leftover cylinder. So
`ψ = ⊔ ψ_{v,a}` has `s(ψ) = X × T` and `r(ψ) ⊊ X × {0}`, and
`h ↦ ψ h ψ^{-1} ⊔ id_{X × {0} \ r(ψ)}` embeds `[[H]]` in `[[H|_{X × {0}}]]`. Hence
`[[G_Λ]] ↪ [[G_{Λ^(n)}]]`.

**Step 4: product with the full 2-shift.** `Λ' = Λ^(n) × B_2` is a finite 3-graph with at
least two loops of each colour at every vertex. By standard facts item 2,
`G_{Λ'} ≅ G_{Λ^(n)} × G_2`. Then `f ↦ f × id` embeds `[[G_{Λ^(n)}]]` in
`S = [[G_{Λ'}]]`.

**Step 5: F_∞.** `li-finite-k-graph-full-groups-are-f-infinity` with `C = Λ'`,
`X = ∂Ω` and all `Y_v = X(v; ∅) = Z(v)`, so `Y` is the whole unit space (standard facts,
item 1). So `S` is of type `F_∞`.

**Step 6: purely infinite and minimal.** Let `U` be compact open and `V ⊇ Z(η)` nonempty.
Write `U = ⊔ Z(μ_i)` (item 3). Pick distinct `τ_i` of a common large degree from `s(η)`,
and `κ_i ∈ s(τ_i) Λ' s(μ_i)`, which exist by strong connectivity. The bisections
`Z(η τ_i κ_i, μ_i)` have disjoint ranges inside `Z(η)` and together have source `U`. So
`G_{Λ'}` is purely infinite minimal in Li's sense, hence has comparison. In Matui's sense:
for a clopen `A`, pick disjoint nonempty clopen `A_1, A_2 ⊆ A` (no isolated points,
item 3) and bisections `A -> A_1`, `A -> A_2`. `G_{Λ'}` is essentially principal on a
Cantor set, because products of aperiodic points are aperiodic and dense (item 4).

**Step 7: homology.** `H_*(G_2) = 0`, so `H_*(G_{Λ'}) = 0` by Künneth
(`matui-groupoid-homology-kunneth-and-full-shift-vanishing`). `C_c(·, Z/2) =
C_c(·, Z) ⊗ Z/2` for totally disconnected spaces and `⊗` is right exact, so
`H_0(G_{Λ'}; Z/2) = H_0(G_{Λ'}) ⊗ Z/2 = 0`. Li's exact sequence
(`li-ah-exact-sequence-for-minimal-comparison-groupoids`) gives
`0 = H_0(G_{Λ'}; Z/2) -> H_1(S) -> H_1(G_{Λ'}) = 0`, so `S` is perfect and `S = D(S)`.

**Step 8: simple.** By `matui-purely-infinite-minimal-full-groups-have-simple-d`,
`D(S) = S` is simple. It is infinite, of type `F_∞`, and contains a copy of `[[G_Λ]]`. □
